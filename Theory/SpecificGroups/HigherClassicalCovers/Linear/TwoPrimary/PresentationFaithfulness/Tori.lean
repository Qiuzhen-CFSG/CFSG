module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.Setup
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.Coordinates

/-!
# Faithfulness on the degree-four torus subgroup

Finite-field torus multiplicativity makes the root tori commute. The
transported three-coordinate identities collect all twelve root tori into
`h₀₁(s) h₁₂(t) h₂₃(u)`. Their diagonal matrix entries detect all three
parameters. This proves faithfulness on the actual torus subgroup, with no
assumption about the rest of the Steinberg presentation.

The proof follows the degree-three development in
`PSL3/UniversalProjection/Faithfulness/Bruhat/Tori.lean`.
Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 38 and
Theorem 8(b), printed p.71 (`refs/KGroup/GLS3/Chapter2St1.tex`).
The Bruhat assembly consumes `torusSubgroup_eq_one_of_matrixMap`.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
open Theory.SpecificGroups.LinearHigher SteinbergWords
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

theorem torus_mul (i j : Fin 4) (hij : i ≠ j) (s t : Fˣ) :
    torus i j hij s * torus i j hij t = torus i j hij (s * t) :=
  torusWord_mul (by decide) i j hij s t

omit [Finite F] in
@[simp] theorem torus_one (i j : Fin 4) (hij : i ≠ j) : torus (F := F) i j hij 1 = 1 :=
  torusWord_one generator_relations i j hij

theorem torus_inv (i j : Fin 4) (hij : i ≠ j) (t : Fˣ) :
    (torus i j hij t)⁻¹ = torus i j hij t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [torus_mul, mul_inv_cancel, torus_one]

omit [Finite F] in
private theorem map_weyl_of_scale
    (f : SteinbergGroup 4 F →* SteinbergGroup 4 F)
    (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) (c : Fˣ)
    (hp : ∀ a, f (generator (root i j hij) a) = generator (root k l hkl) (c * a))
    (hn : ∀ a, f (generator (root j i hij.symm) a) =
      generator (root l k hkl.symm) ((c⁻¹ : Fˣ) * a)) (t : Fˣ) :
    f (weylWord generator i j hij t) = weylWord generator k l hkl (c * t) := by
  simp only [weylWord, map_mul, hp, hn, Units.val_mul]
  congr 2
  simp [mul_comm]

private theorem weyl_mul_weyl_inv (i j : Fin 4) (hij : i ≠ j) (s t : Fˣ) :
    weylWord generator i j hij s * (weylWord generator i j hij t)⁻¹ =
      torus i j hij (s * t⁻¹) := by
  have hi : (torus i j hij t)⁻¹ = torus i j hij t⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [torus_mul, mul_inv_cancel, torus, torusWord_one generator_relations]
  calc
    _ = torus i j hij s * (torus i j hij t)⁻¹ := by
      simp [torus, torusWord, mul_assoc]
    _ = _ := by rw [hi, torus_mul]

private theorem map_torus_of_scale (f : SteinbergGroup 4 F →* SteinbergGroup 4 F)
    (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) (c : Fˣ)
    (hp : ∀ a, f (generator (root i j hij) a) = generator (root k l hkl) (c * a))
    (hn : ∀ a, f (generator (root j i hij.symm) a) =
      generator (root l k hkl.symm) ((c⁻¹ : Fˣ) * a)) (t : Fˣ) :
    f (torus i j hij t) = torus k l hkl t := by
  change f (weylWord generator i j hij t * weylWord generator i j hij (-1)) = _
  rw [map_mul, map_weyl_of_scale f i j k l hij hkl c hp hn,
    map_weyl_of_scale f i j k l hij hkl c hp hn]
  rw [show c * (-1) = -c by simp, ← weylWord_inv generator_relations,
    weyl_mul_weyl_inv]
  congr 1
  simp [mul_assoc]

omit [Finite F] in
theorem torus_conj_weyl (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (s t : Fˣ) :
    MulAut.conj (torus i j hij s) (weylWord generator k l hkl t) =
      weylWord generator k l hkl (rootWeight i j s (root k l hkl) * t) := by
  apply map_weyl_of_scale (MulAut.conj (torus i j hij s)).toMonoidHom
  · intro a
    exact torusWord_conj_generator generator_relations (by decide) i j hij s _ a
  · intro a
    simpa [rootWeight, root, div_eq_mul_inv, mul_comm] using
      torusWord_conj_generator generator_relations (by decide) i j hij s
        (root l k hkl.symm) a

theorem torus_commute (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) (s t : Fˣ) :
    Commute (torus i j hij s) (torus k l hkl t) := by
  change torus i j hij s * torus k l hkl t = torus k l hkl t * torus i j hij s
  have he : MulAut.conj (torus i j hij s) (torus k l hkl t) = torus k l hkl t := by
    apply map_torus_of_scale (MulAut.conj (torus i j hij s)).toMonoidHom
      k l k l hkl hkl (rootWeight i j s (root k l hkl))
    · intro a
      exact torusWord_conj_generator generator_relations (by decide) i j hij s _ a
    · intro a
      simpa [rootWeight, root, div_eq_mul_inv, mul_comm] using
        torusWord_conj_generator generator_relations (by decide) i j hij s
          (root l k hkl.symm) a
  exact mul_inv_eq_iff_eq_mul.mp he


/-- The simple torus parametrization retains the scalar center of SL₄. -/
def simpleTorus (s t u : Fˣ) : SteinbergGroup 4 F :=
  torus 0 1 (by decide) s * torus 1 2 (by decide) t * torus 2 3 (by decide) u

private theorem simpleTorus_mul (s t u a b c : Fˣ) :
    simpleTorus s t u * simpleTorus a b c = simpleTorus (s * a) (t * b) (u * c) := by
  dsimp [simpleTorus]
  have h1 := torus_commute 2 3 0 1 (by decide) (by decide) u a
  have h2 := torus_commute 1 2 0 1 (by decide) (by decide) t a
  have h3 := torus_commute 2 3 1 2 (by decide) (by decide) u b
  rw [(h1.mul_right h3).mul_mul_mul_comm, h2.mul_mul_mul_comm,
    torus_mul, torus_mul, torus_mul]

omit [Finite F] in
@[simp] theorem simpleTorus_one : simpleTorus (1 : Fˣ) 1 1 = 1 := by
  simp [simpleTorus]

private theorem simpleTorus_inv (s t u : Fˣ) :
    (simpleTorus s t u)⁻¹ = simpleTorus s⁻¹ t⁻¹ u⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [simpleTorus_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, simpleTorus_one]

private theorem torus_exists_simpleTorus (r : Root 4) (t : Fˣ) :
    ∃ a b c : Fˣ, torus r.val.1 r.val.2 r.property t = simpleTorus a b c := by
  have h01 (s : Fˣ) : torus 0 1 (by decide) s = simpleTorus s 1 1 := by simp [simpleTorus]
  have h12 (s : Fˣ) : torus 1 2 (by decide) s = simpleTorus 1 s 1 := by simp [simpleTorus]
  have h23 (s : Fˣ) : torus 2 3 (by decide) s = simpleTorus 1 1 s := by simp [simpleTorus]
  have h02 (s : Fˣ) : torus 0 2 (by decide) s = simpleTorus s s 1 := by
    simpa [simpleTorus] using torusWord_chain (0 : Fin 4) 1 2 (by decide) (by decide) (by decide) s
  have h13 (s : Fˣ) : torus 1 3 (by decide) s = simpleTorus 1 s s := by
    simpa [simpleTorus] using torusWord_chain (1 : Fin 4) 2 3 (by decide) (by decide) (by decide) s
  have h03 (s : Fˣ) : torus 0 3 (by decide) s = simpleTorus s s s := by
    rw [show torus 0 3 (by decide) s = torus 0 2 (by decide) s * torus 2 3 (by decide) s from
      torusWord_chain 0 2 3 (by decide) (by decide) (by decide) s, h02]
    simp [simpleTorus]
  obtain ⟨⟨i, j⟩, hij⟩ := r
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨t, 1, 1, h01 t⟩
  · exact ⟨t, t, 1, h02 t⟩
  · exact ⟨t, t, t, h03 t⟩
  · exact ⟨t⁻¹, 1, 1, (torusWord_reverse (by decide) 0 1 (by decide) t).trans (h01 t⁻¹)⟩
  · exact (hij rfl).elim
  · exact ⟨1, t, 1, h12 t⟩
  · exact ⟨1, t, t, h13 t⟩
  · exact ⟨t⁻¹, t⁻¹, 1, (torusWord_reverse (by decide) 0 2 (by decide) t).trans (h02 t⁻¹)⟩
  · exact ⟨1, t⁻¹, 1, (torusWord_reverse (by decide) 1 2 (by decide) t).trans (h12 t⁻¹)⟩
  · exact (hij rfl).elim
  · exact ⟨1, 1, t, h23 t⟩
  · exact ⟨t⁻¹, t⁻¹, t⁻¹, (torusWord_reverse (by decide) 0 3 (by decide) t).trans (h03 t⁻¹)⟩
  · exact ⟨1, t⁻¹, t⁻¹, (torusWord_reverse (by decide) 1 3 (by decide) t).trans (h13 t⁻¹)⟩
  · exact ⟨1, 1, t⁻¹, (torusWord_reverse (by decide) 2 3 (by decide) t).trans (h23 t⁻¹)⟩
  · exact (hij rfl).elim

/-- Every element generated by the twelve root tori collects into three simple tori. -/
theorem torusSubgroup_exists_triple {g : SteinbergGroup 4 F} (hg : g ∈ torusSubgroup F) :
    ∃ s t u : Fˣ, g = simpleTorus s t u := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r, t, rfl⟩ := hg
    exact torus_exists_simpleTorus r t
  | one => exact ⟨1, 1, 1, simpleTorus_one.symm⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨s, t, u, rfl⟩ := ihg
    obtain ⟨a, b, c, rfl⟩ := ihh
    exact ⟨s * a, t * b, u * c, simpleTorus_mul s t u a b c⟩
  | inv g _ ih =>
    obtain ⟨s, t, u, rfl⟩ := ih
    exact ⟨s⁻¹, t⁻¹, u⁻¹, simpleTorus_inv s t u⟩

omit [Finite F] in
theorem matrixMap_torus_zero_one (t : Fˣ) :
    (matrixMap (torus 0 1 (by decide) t) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F), 1, 1] := by
  simp only [torus, torusWord, weylWord, map_mul, matrixMap_generator,
    coe_mul, matrixRoot, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
      Matrix.single, Matrix.one_apply]

omit [Finite F] in
theorem matrixMap_torus_one_two (t : Fˣ) :
    (matrixMap (torus 1 2 (by decide) t) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![1, (t : F), ((t⁻¹ : Fˣ) : F), 1] := by
  simp only [torus, torusWord, weylWord, map_mul, matrixMap_generator,
    coe_mul, matrixRoot, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
      Matrix.single, Matrix.one_apply]

omit [Finite F] in
theorem matrixMap_torus_two_three (t : Fˣ) :
    (matrixMap (torus 2 3 (by decide) t) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![1, 1, (t : F), ((t⁻¹ : Fˣ) : F)] := by
  simp only [torus, torusWord, weylWord, map_mul, matrixMap_generator,
    coe_mul, matrixRoot, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
      Matrix.single, Matrix.one_apply]

omit [Finite F] in
/-- The three simple parameters are detected in SL₄, including central scalar matrices. -/
theorem matrixMap_simpleTorus_eq_one_iff (s t u : Fˣ) :
    matrixMap (simpleTorus s t u) = 1 ↔ s = 1 ∧ t = 1 ∧ u = 1 := by
  constructor
  · intro h
    have hm := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) h
    simp only [simpleTorus, map_mul, coe_mul, matrixMap_torus_zero_one,
      matrixMap_torus_one_two, matrixMap_torus_two_three,
      Matrix.diagonal_mul_diagonal, coe_one] at hm
    have hs := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 0 0) hm
    have ht := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 1 1) hm
    have hu := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 3 3) hm
    simp at hs hu
    refine ⟨hs, ?_, hu⟩
    simpa [hs] using ht
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The matrix kernel is trivial on the literal torus subgroup. -/
theorem torusSubgroup_eq_one_of_matrixMap {g : SteinbergGroup 4 F}
    (hg : g ∈ torusSubgroup F) (hm : matrixMap g = 1) : g = 1 := by
  obtain ⟨s, t, u, rfl⟩ := torusSubgroup_exists_triple hg
  obtain ⟨rfl, rfl, rfl⟩ := (matrixMap_simpleTorus_eq_one_iff s t u).mp hm
  exact simpleTorus_one

/-- A checked restricted faithfulness theorem consumed by the Bruhat assembly. -/
theorem matrixMap_torusSubgroup_injective :
    Function.Injective (matrixMap.comp (torusSubgroup F).subtype) := by
  intro g h he
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  apply torusSubgroup_eq_one_of_matrixMap
    ((torusSubgroup F).mul_mem g.property ((torusSubgroup F).inv_mem h.property))
  change matrixMap g.val = matrixMap h.val at he
  rw [map_mul, map_inv, he, mul_inv_cancel]

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
