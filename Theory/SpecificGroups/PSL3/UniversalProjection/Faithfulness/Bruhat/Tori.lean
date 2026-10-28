module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Setup
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.MatrixComparison

/-!
# Collection into the two simple tori

Assuming multiplicativity of the literal torus words, their conjugation
formulas imply that all root tori commute. Conjugation by a simple Weyl
word then gives `hⱼᵢ(t) = hᵢⱼ(t⁻¹)` and `h₀₂(t) = h₀₁(t) h₁₂(t)`.
Subgroup induction collects every torus word into these two simple tori.
Their diagonal matrix entries give faithfulness on the torus subgroup.

These are the torus-factorization and final diagonal-comparison steps of
Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 38 and Theorem 8(b),
printed p.71 (`refs/KGroup/GLS3/Chapter2St1.tex`). The separate Bruhat
coverage and Weyl-kernel reductions remain necessary for global faithfulness.
-/

@[expose] public section

open Theory.SpecificGroups.LinearHigher SteinbergWords
namespace Matrix.PSL3.UniversalProjection.Faithfulness
variable {F : Type*} [Field F]

private theorem map_weyl_of_scale
    (f : SteinbergGroup 3 F →* SteinbergGroup 3 F)
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (c : Fˣ)
    (hp : ∀ a, f (generator (root i j hij) a) = generator (root k l hkl) (c * a))
    (hn : ∀ a, f (generator (root j i hij.symm) a) =
      generator (root l k hkl.symm) ((c⁻¹ : Fˣ) * a)) (t : Fˣ) :
    f (weylWord generator i j hij t) = weylWord generator k l hkl (c * t) := by
  simp only [weylWord, map_mul, hp, hn, Units.val_mul]
  congr 2
  simp [mul_comm]

private theorem weyl_mul_weyl_inv (hC : TorusMultiplicative F)
    (i j : Fin 3) (hij : i ≠ j) (s t : Fˣ) :
    weylWord generator i j hij s * (weylWord generator i j hij t)⁻¹ =
      torus i j hij (s * t⁻¹) := by
  have hi : (torus i j hij t)⁻¹ = torus i j hij t⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [hC, mul_inv_cancel, torus, torusWord_one generator_relations]
  calc
    _ = torus i j hij s * (torus i j hij t)⁻¹ := by
      simp [torus, torusWord, mul_assoc]
    _ = _ := by rw [hi, hC]

private theorem map_torus_of_scale (hC : TorusMultiplicative F)
    (f : SteinbergGroup 3 F →* SteinbergGroup 3 F)
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (c : Fˣ)
    (hp : ∀ a, f (generator (root i j hij) a) = generator (root k l hkl) (c * a))
    (hn : ∀ a, f (generator (root j i hij.symm) a) =
      generator (root l k hkl.symm) ((c⁻¹ : Fˣ) * a)) (t : Fˣ) :
    f (torus i j hij t) = torus k l hkl t := by
  change f (weylWord generator i j hij t * weylWord generator i j hij (-1)) = _
  rw [map_mul, map_weyl_of_scale f i j k l hij hkl c hp hn,
    map_weyl_of_scale f i j k l hij hkl c hp hn]
  rw [show c * (-1) = -c by simp, ← weylWord_inv generator_relations,
    weyl_mul_weyl_inv hC]
  congr 1
  simp [mul_assoc]

theorem torus_conj_weyl (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
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

theorem torus_commute (hC : TorusMultiplicative F)
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (s t : Fˣ) :
    Commute (torus i j hij s) (torus k l hkl t) := by
  change torus i j hij s * torus k l hkl t = torus k l hkl t * torus i j hij s
  have he : MulAut.conj (torus i j hij s) (torus k l hkl t) = torus k l hkl t := by
    apply map_torus_of_scale hC (MulAut.conj (torus i j hij s)).toMonoidHom
      k l k l hkl hkl (rootWeight i j s (root k l hkl))
    · intro a
      exact torusWord_conj_generator generator_relations (by decide) i j hij s _ a
    · intro a
      simpa [rootWeight, root, div_eq_mul_inv, mul_comm] using
        torusWord_conj_generator generator_relations (by decide) i j hij s
          (root l k hkl.symm) a
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem weyl_conj_torus_self (hC : TorusMultiplicative F)
    (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) :
    MulAut.conj (weylWord generator i j hij 1) (torus i j hij t) =
      torus j i hij.symm t := by
  apply map_torus_of_scale hC (MulAut.conj (weylWord generator i j hij 1)).toMonoidHom
    i j j i hij hij.symm (-1)
  · intro a
    simpa using weylWord_conj_root generator_relations (by decide) i j hij 1 a
  · intro a
    simpa using weylWord_conj_opposite_root generator_relations (by decide) i j hij 1 a

private theorem weyl_conj_torus_zero_one (hC : TorusMultiplicative F) (t : Fˣ) :
    MulAut.conj (weylWord generator 1 2 (by decide) 1) (torus 0 1 (by decide) t) =
      torus 0 2 (by decide) t := by
  apply map_torus_of_scale hC
    (MulAut.conj (weylWord generator 1 2 (by decide) 1)).toMonoidHom
    0 1 0 2 (by decide) (by decide) (-1)
  · intro a
    simpa using weylWord_conj_other_incoming generator_relations
      (1 : Fin 3) 2 0 (by decide) (by decide) (by decide) (1 : Fˣ) a
  · intro a
    simpa using weylWord_conj_outgoing generator_relations
      (1 : Fin 3) 2 0 (by decide) (by decide) (by decide) (1 : Fˣ) a

/-- The simple Weyl action on a root torus is a product of two torus words.
This formula does not use torus multiplicativity. -/
theorem weyl_conj_torus_formula
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) (s : Fˣ) :
    MulAut.conj (weylWord generator k l hkl 1) (torus i j hij s) =
      (torus k l hkl (rootWeight i j s (root k l hkl)))⁻¹ * torus i j hij s := by
  have he : torus i j hij s *
      (MulAut.conj (weylWord generator k l hkl 1) (torus i j hij s))⁻¹ =
      torus k l hkl (rootWeight i j s (root k l hkl)) := by
    calc
      _ = MulAut.conj (torus i j hij s) (weylWord generator k l hkl 1) *
          (weylWord generator k l hkl 1)⁻¹ := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = _ := by
        rw [torus_conj_weyl, mul_one, weylWord_inv generator_relations]
        rfl
  calc
    _ = (torus i j hij s *
        (MulAut.conj (weylWord generator k l hkl 1) (torus i j hij s))⁻¹)⁻¹ *
        torus i j hij s := by group
    _ = _ := by rw [he]

theorem torus_inv (hC : TorusMultiplicative F)
    (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) :
    (torus i j hij t)⁻¹ = torus i j hij t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [hC, mul_inv_cancel, torus, torusWord_one generator_relations]

theorem torus_reverse (hC : TorusMultiplicative F)
    (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) :
    torus j i hij.symm t = torus i j hij t⁻¹ := by
  rw [← weyl_conj_torus_self hC i j hij t, weyl_conj_torus_formula, torus_inv hC, hC]
  congr 1
  simp [rootWeight, torusWeight, root, hij.symm]

theorem torus_zero_two (hC : TorusMultiplicative F) (t : Fˣ) :
    torus 0 2 (by decide) t = torus 0 1 (by decide) t * torus 1 2 (by decide) t := by
  rw [← weyl_conj_torus_zero_one hC, weyl_conj_torus_formula, torus_inv hC]
  have hc : (rootWeight (0 : Fin 3) 1 t (root 1 2 (by decide)))⁻¹ = t := by
    simp [rootWeight, torusWeight, root]
  rw [hc]
  exact (torus_commute hC 1 2 0 1 (by decide) (by decide) t t).eq

private def simpleTorusPair (s t : Fˣ) : SteinbergGroup 3 F :=
  torus 0 1 (by decide) s * torus 1 2 (by decide) t

private theorem simpleTorusPair_mul (hC : TorusMultiplicative F) (s t u v : Fˣ) :
    simpleTorusPair s t * simpleTorusPair u v = simpleTorusPair (s * u) (t * v) := by
  dsimp [simpleTorusPair]
  rw [mul_assoc, ← mul_assoc (torus 1 2 (by decide) t),
    (torus_commute hC 1 2 0 1 (by decide) (by decide) t u).eq,
    mul_assoc, ← mul_assoc, hC, hC]

private theorem simpleTorusPair_one : simpleTorusPair (1 : Fˣ) 1 = 1 := by
  simp [simpleTorusPair, torus, torusWord_one generator_relations]

private theorem simpleTorusPair_inv (hC : TorusMultiplicative F) (s t : Fˣ) :
    (simpleTorusPair s t)⁻¹ = simpleTorusPair s⁻¹ t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [simpleTorusPair_mul hC, mul_inv_cancel, mul_inv_cancel, simpleTorusPair_one]

private theorem torus_exists_simpleTorusPair (hC : TorusMultiplicative F)
    (r : Root 3) (t : Fˣ) : ∃ s u : Fˣ, torus r.val.1 r.val.2 r.property t = simpleTorusPair s u := by
  have hp (s : Fˣ) : torus 0 1 (by decide) s = simpleTorusPair s 1 := by
    simp [simpleTorusPair, torus, torusWord_one generator_relations]
  have hq (s : Fˣ) : torus 1 2 (by decide) s = simpleTorusPair 1 s := by
    simp [simpleTorusPair, torus, torusWord_one generator_relations]
  have hr (s : Fˣ) : torus 0 2 (by decide) s = simpleTorusPair s s := torus_zero_two hC s
  obtain ⟨⟨i, j⟩, hij⟩ := r
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨t, 1, hp t⟩
  · exact ⟨t, t, hr t⟩
  · exact ⟨t⁻¹, 1, (torus_reverse hC 0 1 (by decide) t).trans (hp t⁻¹)⟩
  · exact (hij rfl).elim
  · exact ⟨1, t, hq t⟩
  · exact ⟨t⁻¹, t⁻¹, (torus_reverse hC 0 2 (by decide) t).trans (hr t⁻¹)⟩
  · exact ⟨1, t⁻¹, (torus_reverse hC 1 2 (by decide) t).trans (hq t⁻¹)⟩
  · exact (hij rfl).elim

/-- Every element of the subgroup generated by all root tori is a product
of the two simple-root torus words, assuming relation (C). -/
theorem torusSubgroup_exists_pair (hC : TorusMultiplicative F)
    {g : SteinbergGroup 3 F} (hg : g ∈ torusSubgroup F) :
    ∃ s t : Fˣ, g = torus 0 1 (by decide) s * torus 1 2 (by decide) t := by
  change ∃ s t : Fˣ, g = simpleTorusPair s t
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r, t, rfl⟩ := hg
    exact torus_exists_simpleTorusPair hC r t
  | one => exact ⟨1, 1, simpleTorusPair_one.symm⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨s, t, rfl⟩ := ihg
    obtain ⟨u, v, rfl⟩ := ihh
    exact ⟨s * u, t * v, simpleTorusPair_mul hC s t u v⟩
  | inv g _ ih =>
    obtain ⟨s, t, rfl⟩ := ih
    exact ⟨s⁻¹, t⁻¹, simpleTorusPair_inv hC s t⟩

/-- Application of simple-torus collection to the literal matrix kernel. -/
theorem torusSubgroup_eq_one_of_matrixMap (hC : TorusMultiplicative F)
    {g : SteinbergGroup 3 F} (hg : g ∈ torusSubgroup F) (hm : matrixMap g = 1) : g = 1 := by
  obtain ⟨s, t, rfl⟩ := torusSubgroup_exists_pair hC hg
  obtain ⟨rfl, rfl⟩ := (matrixMap_torus_pair_eq_one_iff s t).mp hm
  simp [torus, torusWord_one generator_relations]

/-- Under relation (C), the actual matrix map is faithful on the torus subgroup. -/
theorem matrixMap_torusSubgroup_injective (hC : TorusMultiplicative F) :
    Function.Injective (matrixMap.comp (torusSubgroup F).subtype) := by
  intro g h he
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  apply torusSubgroup_eq_one_of_matrixMap hC
    ((torusSubgroup F).mul_mem g.property ((torusSubgroup F).inv_mem h.property))
  change matrixMap g.val = matrixMap h.val at he
  rw [map_mul, map_inv, he, mul_inv_cancel]
end Matrix.PSL3.UniversalProjection.Faithfulness
