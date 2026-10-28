module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.UnipotentGeometry

/-!
# Simultaneous normalization of opposite unipotent subgroups in PSL₃

An automorphism first carries the upper unitriangular Sylow subgroup back to
itself by inner conjugation. Its image of the lower subgroup is another Sylow
subgroup disjoint from the upper one. We prove directly that every such Sylow
can be carried to the specified lower subgroup by an upper unitriangular element.

The matrix argument is the open Bruhat cell in degree three. If a conjugating
matrix g has zero bottom-left entry, its first column constructs a nonidentity
upper transvection in the intersection. Applying this observation also to g⁻¹
makes both corner pivots nonzero. The upper unitriangular correction has first
row equal to the last row of g⁻¹ divided by its first entry, and its (1,2) entry
kills the middle entry of the first column of g. Thus the corrected flag is the
opposite flag. A signed reversal identifies its unipotent group with the actual
inverse-transpose image used in `PreservesUnipotentPair`.

Scalar ambiguity is removed by the literal upper and lower matrix entries.
There is no division by 3, so the argument includes characteristic three.
The geometric argument needs no simplicity, nonsolvability, or oddness; the
final wrapper retains those inputs of the automorphism-coverage consumer.

Source: GLS3, §§2.3 and 2.7, as a step toward Theorem 2.5.12(a),
`refs/KGroup/GLS3/chapter2.tex`, especially lines 1111–1115.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage.OppositePair
variable (F : Type*) [Field F]

private theorem graphSL_val (u : SL(3,F)) :
    (graphSL F u).val = u⁻¹.val.transpose := by
  have he : SpecialLinearGroup.transpose u⁻¹ =
      (SpecialLinearGroup.transpose u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Subtype.ext
    change u⁻¹.val.transpose * u.val.transpose = 1
    rw [← Matrix.transpose_mul]
    have h : u.val * u⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel u)
    rw [h, Matrix.transpose_one]
  exact congrArg (fun x : SL(3,F) => x.val) he.symm

/-- The determinant-one representative of the longest Weyl element. -/
private def longest : SL(3,F) :=
  ⟨!![0,0,1; 0,-1,0; 1,0,0], by simp [Matrix.det_fin_three]⟩

private theorem longest_sq : longest F * longest F = 1 := by
  apply Subtype.ext
  change (longest F).val * (longest F).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longest, Matrix.mul_apply, Fin.sum_univ_three]

private theorem longest_inv : (longest F)⁻¹ = longest F :=
  inv_eq_of_mul_eq_one_right (longest_sq F)

private theorem upper_mem (a b c : F) :
    specialLinear F ⟨a,b,c⟩ ∈ unipotentSL F :=
  (specialLinear_range F).le ⟨⟨a,b,c⟩, rfl⟩

private theorem lower_eq_longest_map :
    lowerUnipotent F =
      (upperUnipotent F).map (MulAut.conj (projection F (longest F))).toMonoidHom := by
  have he : (unipotentSL F).map (graphSL F).toMonoidHom =
      (unipotentSL F).map (MulAut.conj (longest F)).toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨u,hu,rfl⟩
      obtain ⟨v, hv⟩ := (show u⁻¹ ∈ (specialLinear F).range by
        rw [specialLinear_range]; exact (unipotentSL F).inv_mem hu)
      refine ⟨specialLinear F ⟨-v.y,-v.x,v.c⟩, upper_mem F _ _ _, ?_⟩
      apply Subtype.ext
      change (longest F * specialLinear F _ * (longest F)⁻¹).val = (graphSL F u).val
      rw [graphSL_val, ← hv]
      rw [longest_inv]
      change ((longest F).val * matrix F _ * (longest F).val) = (matrix F _)ᵀ
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [longest, matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · rintro _ ⟨u,hu,rfl⟩
      obtain ⟨v,rfl⟩ := (specialLinear_range F).symm ▸ hu
      refine ⟨(specialLinear F ⟨-v.y,-v.x,v.c⟩)⁻¹,
        (unipotentSL F).inv_mem (upper_mem F _ _ _), ?_⟩
      apply Subtype.ext
      change (graphSL F ((specialLinear F _)⁻¹)).val =
        (longest F * specialLinear F _ * (longest F)⁻¹).val
      rw [graphSL_val, inv_inv]
      rw [longest_inv]
      change (matrix F _)ᵀ = ((longest F).val * matrix F _ * (longest F).val)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [longest, matrix, Matrix.mul_apply, Fin.sum_univ_three]
  have hp := congrArg (fun S : Subgroup SL(3,F) => S.map (projection F)) he
  have hc : (projection F).comp (MulAut.conj (longest F)).toMonoidHom =
      (MulAut.conj (projection F (longest F))).toMonoidHom.comp (projection F) := by
    ext x
    simp [MulAut.conj_apply]
  have hg : (projection F).comp (graphSL F).toMonoidHom =
      (graph F).toMonoidHom.comp (projection F) := rfl
  simpa only [lowerUnipotent, upperUnipotent, unipotent, Subgroup.map_map, hc, hg] using hp

private theorem projection_eq_scalar (u v : SL(3,F))
    (h : projection F u = projection F v) : ∃ r : F, u.val = r • v.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    u.val = (v * (v⁻¹ * u)).val := by simp
    _ = v.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • v.val := by ext i j; simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

/-- The two specified unitriangular images meet trivially in PSL₃. -/
theorem disjoint_upper_lower : Disjoint (upperUnipotent F) (lowerUnipotent F) := by
  rw [Subgroup.disjoint_def]
  intro x hx hy
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨_,⟨v,hv,rfl⟩,he⟩ := hy
  change projection F (graphSL F v) = projection F u at he
  obtain ⟨r,hr⟩ := projection_eq_scalar F u (graphSL F v) he.symm
  have hu' := (mem_unipotentSL_iff F u).mp hu
  have hv' := (mem_unipotentSL_iff F v⁻¹).mp ((unipotentSL F).inv_mem hv)
  rw [graphSL_val, hv', hu'] at hr
  have h01 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 1) hr
  have h02 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 2) hr
  have h12 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 2) hr
  simp at h01 h02 h12
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [hu',h01,h02,h12]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hu1,map_one]

/-- A vanishing bottom-left entry produces a nonidentity element in the
intersection of the upper group and its conjugate. -/
private theorem bottom_left_ne_zero_of_disjoint (g : SL(3,F))
    (hd : Disjoint (upperUnipotent F)
      ((upperUnipotent F).map (MulAut.conj (projection F g)).toMonoidHom)) :
    g.val 2 0 ≠ 0 := by
  intro hg
  let u : U F := ⟨0,g.val 1 0,g.val 0 0⟩
  let v : U F := ⟨g.val 2 1,0,g.val 2 2⟩
  have hmul : specialLinear F u * g = g * specialLinear F v := by
    apply Subtype.ext
    change matrix F u * g.val = g.val * matrix F v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u,v,matrix,Matrix.mul_apply,Fin.sum_univ_three,hg] <;> ring
  have hconj : g * specialLinear F v * g⁻¹ = specialLinear F u := by
    rw [← hmul, mul_inv_cancel_right]
  have hu : projection F (specialLinear F u) ∈ upperUnipotent F :=
    Subgroup.mem_map_of_mem _ (upper_mem F _ _ _)
  have hv : projection F (specialLinear F u) ∈
      (upperUnipotent F).map (MulAut.conj (projection F g)).toMonoidHom := by
    refine ⟨projection F (specialLinear F v),
      Subgroup.mem_map_of_mem _ (upper_mem F _ _ _), ?_⟩
    change projection F g * projection F (specialLinear F v) * (projection F g)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  have h1 := Subgroup.disjoint_def.mp hd hu hv
  have hu1 : u = 1 := projective_injective F (h1.trans (map_one (projective F)).symm)
  have h00 : g.val 0 0 = 0 := congrArg U.c hu1
  have h10 : g.val 1 0 = 0 := congrArg U.y hu1
  have hdet := g.property
  rw [Matrix.det_fin_three, hg, h00, h10] at hdet
  simp at hdet

private theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_inv_cancel {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul, inv_mul_cancel]
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext z
    simp
  rw [he, H.map_id]

/-- The two corner pivots put the transported flag in the open cell. -/
private theorem exists_upper_correction [Finite F] (g : SL(3,F))
    (hg : g.val 2 0 ≠ 0) (hi : g⁻¹.val 2 0 ≠ 0) :
    ∃ b ∈ unipotentSL F, longest F * (b * g) ∈ borelSL F := by
  let b := specialLinear F ⟨g⁻¹.val 2 1 / g⁻¹.val 2 0,
    -g.val 1 0 / g.val 2 0, g⁻¹.val 2 2 / g⁻¹.val 2 0⟩
  refine ⟨b, upper_mem F _ _ _, ?_⟩
  have hcol (j : Fin 3) (hj : j ≠ 2) :
      g⁻¹.val 2 0 * g.val 0 j + g⁻¹.val 2 1 * g.val 1 j +
        g⁻¹.val 2 2 * g.val 2 j = 0 := by
    have h := congrArg (fun x : SL(3,F) => x.val 2 j) (inv_mul_cancel g)
    change (g⁻¹.val * g.val) 2 j = (1 : Matrix (Fin 3) (Fin 3) F) 2 j at h
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      if_neg (Ne.symm hj)] using h
  have hb0 (j : Fin 3) (hj : j ≠ 2) : (b * g).val 0 j = 0 := by
    change (matrix F _ * g.val) 0 j = 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    change 1 * g.val 0 j + g⁻¹.val 2 1 / g⁻¹.val 2 0 * g.val 1 j +
      g⁻¹.val 2 2 / g⁻¹.val 2 0 * g.val 2 j = 0
    rw [one_mul]
    apply (mul_left_cancel₀ hi)
    calc
      g⁻¹.val 2 0 * (g.val 0 j + g⁻¹.val 2 1 / g⁻¹.val 2 0 * g.val 1 j +
          g⁻¹.val 2 2 / g⁻¹.val 2 0 * g.val 2 j) =
          g⁻¹.val 2 0 * g.val 0 j + g⁻¹.val 2 1 * g.val 1 j +
          g⁻¹.val 2 2 * g.val 2 j := by field_simp
      _ = _ := by simpa using hcol j hj
  have hb10 : (b * g).val 1 0 = 0 := by
    change (matrix F _ * g.val) 1 0 = 0
    simp [matrix,Matrix.mul_apply,Fin.sum_univ_three,hg]
  rw [mem_borelSL_iff]
  change ((longest F).val * (b * g).val) 1 0 = 0 ∧
    ((longest F).val * (b * g).val) 2 0 = 0 ∧
    ((longest F).val * (b * g).val) 2 1 = 0
  generalize (b * g).val = c at hb0 hb10 ⊢
  simp [longest,Matrix.mul_apply,Fin.sum_univ_three,hb0 0 (by decide),hb0 1 (by decide),hb10]

variable [Finite F]

/-- Every conjugate disjoint from the upper unipotent group can be sent to its
specified lower opposite by an element of the upper group itself. -/
theorem exists_unipotent_conjugator (g : PSL(3,F))
    (hd : Disjoint (upperUnipotent F)
      ((upperUnipotent F).map (MulAut.conj g).toMonoidHom)) :
    ∃ b ∈ upperUnipotent F,
      ((upperUnipotent F).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj b).toMonoidHom = lowerUnipotent F := by
  obtain ⟨g,rfl⟩ := projection_surjective F g
  have hi : Disjoint (upperUnipotent F)
      ((upperUnipotent F).map (MulAut.conj (projection F g⁻¹)).toMonoidHom) := by
    have h := (Subgroup.disjoint_map (f := (MulAut.conj (projection F g)⁻¹).toMonoidHom)
      (MulAut.conj (projection F g)⁻¹).injective hd).symm
    rw [map_conj_inv_cancel] at h
    simpa only [map_inv] using h
  obtain ⟨b,hb,hbg⟩ := exists_upper_correction F g
    (bottom_left_ne_zero_of_disjoint F g hd) (bottom_left_ne_zero_of_disjoint F g⁻¹ hi)
  refine ⟨projection F b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  have hn : (upperUnipotent F).map
      (MulAut.conj (projection F (longest F * (b * g)))).toMonoidHom = upperUnipotent F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (borel_le_normalizer_unipotent F (Subgroup.mem_map_of_mem _ hbg))
  have he : b * g = longest F * (longest F * (b * g)) := by
    rw [← mul_assoc, longest_sq, one_mul]
  rw [← map_conj_mul, ← map_mul, he, map_mul, map_conj_mul, hn,
    ← lower_eq_longest_map]

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage.OppositePair

namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable (F : Type*) [Field F] [Finite F]

/-- Sylow conjugacy followed by the open-cell correction fixes both members of
the specified opposite pair. -/
theorem exists_inner_preserves_pair_of_prime_card {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p) (α : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), PreservesUnipotentPair F (MulAut.conj g * α) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_inner_preserves_upper F hp hF α
  let β : MulAut PSL(3,F) := MulAut.conj a * α
  have hd : Disjoint (upperUnipotent F) ((lowerUnipotent F).map β.toMonoidHom) := by
    have h := Subgroup.disjoint_map (f := β.toMonoidHom) β.injective
      (OppositePair.disjoint_upper_lower F)
    change Disjoint ((upperUnipotent F).map (MulAut.conj a * α).toMonoidHom) _ at h
    rwa [ha] at h
  let V : Sylow p PSL(3,F) :=
    (lowerSylow F hp hF).mapSurjective (f := β.toMonoidHom) β.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (upperSylow F hp hF) V
  have hs : (upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      (lowerUnipotent F).map β.toMonoidHom :=
    congrArg (fun S : Sylow p PSL(3,F) => (S : Subgroup PSL(3,F))) hg
  obtain ⟨b,hb,hbl⟩ := OppositePair.exists_unipotent_conjugator F g (hs.symm ▸ hd)
  rw [hs] at hbl
  have hbu : (upperUnipotent F).map (MulAut.conj b).toMonoidHom = upperUnipotent F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((upperUnipotent F).le_normalizer hb)
  have he (H : Subgroup PSL(3,F)) :
      H.map (MulAut.conj (b * a) * α).toMonoidHom =
        (H.map β.toMonoidHom).map (MulAut.conj b).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [β, MulAut.conj_apply, mul_assoc]
  refine ⟨b * a, ?_, ?_⟩
  · rw [he]
    change ((upperUnipotent F).map (MulAut.conj a * α).toMonoidHom).map _ = _
    rw [ha,hbu]
  · rw [he]
    exact hbl

/-- The opposite-pair normalization required by odd-prime PSL₃ automorphism
coverage, including p = 3. Simplicity and nonsolvability are inherited inputs;
the normalization itself holds without these extra restrictions. -/
theorem exists_inner_preserves_pair [IsSimpleGroup PSL(3,F)]
    (_hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (_hodd : Odd p) (hF : Nat.card F = p) (α : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), PreservesUnipotentPair F (MulAut.conj g * α) :=
  exists_inner_preserves_pair_of_prime_card F hp hF α

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
