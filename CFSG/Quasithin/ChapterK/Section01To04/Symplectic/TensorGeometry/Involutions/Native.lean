module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Coordinates
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions.RootIdentification
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction

/-!
# Native involutions on the descended symplectic tensor

Apply the group-theoretic central normal form to the genuine coefficient-twisted
tensor, then descend its fixed dimensions through the published intertwiner.
The Suzuki types b₁, a₂ and c₂ fix respectively 10s, 8s and 8s binary dimensions.
For the last two types, rank-nullity and involutivity identify the fixed space
with the displacement image on the original module. The ambient-subgroup
adapters retain the literal element j and representation ρ.

No diagram-preservation or ambient-normalizer hypothesis is used here.
Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open scoped Matrix TensorProduct Classical
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
open SymplecticConjugatePair.Involutions
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

lemma isB1_tensor_fixed_finrank {n : ℕ} (hF : Nat.card F = 2^n)
    (σ : F ≃+* F) (j : Sp F) (hj : IsB1 j) :
    Module.finrank F (invariants ((twistedTensor σ).comp (Subgroup.zpowers j).subtype)) = 10 := by
  obtain ⟨c,a,b,he⟩ := involution_conjugate_central hF j hj.1
  have hz := (isB1_conj_iff c j).mpr hj
  rw [he,central_isB1_iff] at hz
  obtain ⟨ha,rfl⟩ := hz
  rw [(cyclicInvariantsConj (twistedTensor σ) j c).finrank_eq, he]
  exact central_fixed_finrank_of_right_zero σ ha

lemma nonB1_tensor_fixed_finrank {n : ℕ} (hF : Nat.card F = 2^n)
    (σ : F ≃+* F) (j : Sp F) (hj : orderOf j = 2) (hB : ¬ IsB1 j) :
    Module.finrank F (invariants ((twistedTensor σ).comp (Subgroup.zpowers j).subtype)) = 8 := by
  obtain ⟨c,a,b,he⟩ := involution_conjugate_central hF j hj
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := by
      intro ha
      have ho := (MulAut.conj c).orderOf_eq j
      change orderOf (c*j*c⁻¹) = orderOf j at ho
      rw [he,ha,hb] at ho
      simp [RootSubgroup.element_zero,hj] at ho
    apply hB
    apply (isB1_conj_iff c j).mp
    rw [he,hb]
    exact central_isB1 ha
  rw [(cyclicInvariantsConj (twistedTensor σ) j c).finrank_eq, he]
  exact central_fixed_finrank_of_right_ne_zero σ a hb
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- Native involution dimensions on the descended tensor; no ambient
normalizer or diagram-preservation hypothesis is used. -/
theorem TensorIdentification.involution_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) =
      if IsB1 (h.groupEquiv j) then 10*s else 8*s := by
  classical
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hd := h.fixed_finrank ρ (Subgroup.zpowers (h.groupEquiv j))
  have hm := h.groupEquiv.symm.toMonoidHom.map_zpowers (h.groupEquiv j)
  change (Subgroup.zpowers (h.groupEquiv j)).map h.groupEquiv.symm.toMonoidHom =
    Subgroup.zpowers (h.groupEquiv.symm (h.groupEquiv j)) at hm
  rw [MulEquiv.symm_apply_apply] at hm
  rw [hm] at hd
  rw [hd]
  by_cases hB : IsB1 (h.groupEquiv j)
  · rw [if_pos hB, TensorGeometry.isB1_tensor_fixed_finrank h.field_card _ _ hB]
    omega
  · rw [if_neg hB, TensorGeometry.nonB1_tensor_fixed_finrank h.field_card _ _
      ((h.groupEquiv.orderOf_eq j).trans hj) hB]
    omega

theorem TensorIdentification.isB1_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : IsB1 (h.groupEquiv j)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 10*s := by
  have ho : orderOf j = 2 := (h.groupEquiv.orderOf_eq j).symm.trans hj.1
  rw [h.involution_fixed_finrank ρ j ho, if_pos hj]

theorem TensorIdentification.isA2_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : IsA2 (h.groupEquiv j)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 8*s := by
  have ho : orderOf j = 2 := (h.groupEquiv.orderOf_eq j).symm.trans hj.1
  have hn : ¬ IsB1 (h.groupEquiv j) := by
    intro hB
    have h1 := hB.2
    have h2 := hj.2.1
    omega
  rw [h.involution_fixed_finrank ρ j ho, if_neg hn]

theorem TensorIdentification.isC2_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : IsC2 (h.groupEquiv j)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 8*s := by
  have ho : orderOf j = 2 := (h.groupEquiv.orderOf_eq j).symm.trans hj.1
  have hn : ¬ IsB1 (h.groupEquiv j) := by
    intro hB
    have h1 := hB.2
    have h2 := hj.2.1
    omega
  rw [h.involution_fixed_finrank ρ j ho, if_neg hn]

theorem TensorIdentification.involution_fixed_finrank_le {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) ≤ 10*s := by
  rw [h.involution_fixed_finrank ρ j hj]
  split_ifs <;> omega

/-- Freeness is the intrinsic equality of the fixed space and displacement
image, on the original binary module. -/
theorem TensorIdentification.nonB1_fixedSpace_eq_displacement {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv j)) :
    fixedSpace ρ (Subgroup.zpowers j) = LinearMap.range (displacement ρ j) := by
  have hi : LinearMap.range (displacement ρ j) ≤ fixedSpace ρ (Subgroup.zpowers j) := by
    rintro _ ⟨v,rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    exact involution_fixes_displacement ρ
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hj).1) v
  apply (Submodule.eq_of_le_of_finrank_eq hi ?_).symm
  have hd := fixedCodim_add_finrank ρ (Subgroup.zpowers j)
  have hf := h.involution_fixed_finrank ρ j hj
  rw [if_neg hB] at hf
  rw [h.binary_finrank, hf, fixedCodim_zpowers_eq_displacement_rank] at hd
  change Module.finrank (ZMod 2) (LinearMap.range (displacement ρ j)) + 8*s = 16*s at hd
  rw [hf]
  omega
end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

omit [Finite G] [FiniteDimensional (ZMod 2) V] [IsIrreducible (ρ.comp L.subtype)] in
private lemma component_cyclic_fixedSpace (j : L) :
    fixedSpace (ρ.comp L.subtype) (Subgroup.zpowers j) =
      fixedSpace ρ (Subgroup.zpowers j.val) := by
  ext v
  simp only [mem_fixedSpace_zpowers_iff, MonoidHom.comp_apply, Subgroup.coe_subtype]

/-- The native bound in the literal ambient action, as required by the
local premise of `TensorIdentification.quadraticRatio_gt_two`. -/
theorem TensorIdentification.component_involution_fixed_finrank_le {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) ≤ 10*s := by
  have ho : orderOf (⟨j,hjL⟩ : L) = 2 := (Subgroup.orderOf_coe (⟨j,hjL⟩ : L)).symm.trans hj
  rw [← component_cyclic_fixedSpace ρ L ⟨j,hjL⟩]
  exact h.involution_fixed_finrank_le (ρ.comp L.subtype) _ ho

theorem TensorIdentification.component_isB1_fixed_finrank {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : IsB1 (h.groupEquiv ⟨j,hjL⟩)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 10*s := by
  rw [← component_cyclic_fixedSpace ρ L ⟨j,hjL⟩]
  exact h.isB1_fixed_finrank (ρ.comp L.subtype) _ hj

theorem TensorIdentification.component_isA2_fixed_finrank {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : IsA2 (h.groupEquiv ⟨j,hjL⟩)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 8*s := by
  rw [← component_cyclic_fixedSpace ρ L ⟨j,hjL⟩]
  exact h.isA2_fixed_finrank (ρ.comp L.subtype) _ hj

theorem TensorIdentification.component_isC2_fixed_finrank {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : IsC2 (h.groupEquiv ⟨j,hjL⟩)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) = 8*s := by
  rw [← component_cyclic_fixedSpace ρ L ⟨j,hjL⟩]
  exact h.isC2_fixed_finrank (ρ.comp L.subtype) _ hj

/-- Freeness on the component is the same equality of subspaces in the
ambient representation, not merely an equality of dimensions. -/
theorem TensorIdentification.component_nonB1_fixedSpace_eq_displacement {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv ⟨j,hjL⟩)) :
    fixedSpace ρ (Subgroup.zpowers j) = LinearMap.range (displacement ρ j) := by
  have ho : orderOf (⟨j,hjL⟩ : L) = 2 := (Subgroup.orderOf_coe (⟨j,hjL⟩ : L)).symm.trans hj
  rw [← component_cyclic_fixedSpace ρ L ⟨j,hjL⟩]
  exact h.nonB1_fixedSpace_eq_displacement (ρ.comp L.subtype) _ ho hB

theorem TensorIdentification.component_isA2_fixedSpace_eq_displacement {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : IsA2 (h.groupEquiv ⟨j,hjL⟩)) :
    fixedSpace ρ (Subgroup.zpowers j) = LinearMap.range (displacement ρ j) := by
  apply h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL
  · exact (Subgroup.orderOf_coe (⟨j,hjL⟩ : L)).trans
      ((h.groupEquiv.orderOf_eq _).symm.trans hj.1)
  · intro hB
    have h1 := hB.2
    have h2 := hj.2.1
    omega

theorem TensorIdentification.component_isC2_fixedSpace_eq_displacement {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : IsC2 (h.groupEquiv ⟨j,hjL⟩)) :
    fixedSpace ρ (Subgroup.zpowers j) = LinearMap.range (displacement ρ j) := by
  apply h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL
  · exact (Subgroup.orderOf_coe (⟨j,hjL⟩ : L)).trans
      ((h.groupEquiv.orderOf_eq _).symm.trans hj.1)
  · intro hB
    have h1 := hB.2
    have h2 := hj.2.1
    omega
end CFSG.Quasithin.ChapterK.Symplectic

