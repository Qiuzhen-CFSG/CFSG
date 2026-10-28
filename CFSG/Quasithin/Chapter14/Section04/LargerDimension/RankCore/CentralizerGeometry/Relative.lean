module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Relative centralizers for a source pair of extraspecial subgroups

Right conjugation is A^g = g⁻¹Ag. The subgroup D is C_{H^g}(U^g),
whereas W = C_U(V₂). The earlier identities H=C_G(V₁) and V₂≤U^g
place D in H. Mutual normalization puts [D,W] inside C_W(U^g).
The exact symmetric 12.8.9(5) quotient-action kernel then puts that
centralizer inside U^g, giving [D,W]≤Z(U^g).

`QuotientKernel` retains the whole equivalence in 12.8.9(5), including
the literal intersection E. In particular it is not a substitute which
assumes the centralizer conclusion of 14.4.7.

Source: Aschbacher--Smith, 12.8.9(5), printed p.853, and the opening
paragraph of 14.4.7, printed pp.1008--1009.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
variable {G : Type*} [Group G]

def conjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

def D (H U : Subgroup G) (g : G) : Subgroup G :=
  conjugate H g ⊓ centralizer (conjugate U g : Set G)

def W (U V₂ : Subgroup G) : Subgroup G := U ⊓ centralizer (V₂ : Set G)

def Z (U : Subgroup G) : Subgroup G := (center U).map U.subtype

theorem center_image (U : Subgroup G) : Z U = U ⊓ centralizer (U : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.property, ?_⟩
    intro u hu
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩)
  · rintro ⟨hxU, hxC⟩
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro u
    exact Subtype.ext (hxC u u.property)

theorem centralizer_map (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro a ha
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

theorem conjugate_centralizer (A : Subgroup G) (g : G) :
    conjugate (centralizer (A : Set G)) g = centralizer (conjugate A g : Set G) :=
  centralizer_map A (MulAut.conj g⁻¹)

theorem relative_centralizer_normalized (H U : Subgroup G)
    (hHU : H ≤ normalizer (U : Set G)) :
    H ≤ normalizer (H ⊓ centralizer (U : Set G) : Set G) :=
  (le_inf H.le_normalizer
    (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
    inf_normalizer_le_normalizer_inf

/-- The literal 12.8.9(5) kernel statement for the symmetric pair U,P.
Its right side is E=W∩C_P(V₂). -/
def QuotientKernel (U P V₂ : Subgroup G) : Prop :=
  ∀ w ∈ W U V₂, (∀ u ∈ P, ⁅w, u⁆ ∈ Z P) ↔ w ∈ W U V₂ ⊓ W P V₂

theorem relative_centralizer_le (H J P A V₂ : Subgroup G)
    (hH : H = centralizer (A : Set G)) (hA : A ≤ V₂) (hVP : V₂ ≤ P) :
    J ⊓ centralizer (P : Set G) ≤ H := by
  rw [hH]
  exact inf_le_right.trans (centralizer_le (hA.trans hVP))

theorem relative_commutator_le_center (H J U P A B V₂ : Subgroup G)
    (hH : H = centralizer (A : Set G)) (hJ : J = centralizer (B : Set G))
    (hA : A ≤ V₂) (hB : B ≤ V₂) (hVP : V₂ ≤ P)
    (hHU : H ≤ normalizer (U : Set G)) (hJP : J ≤ normalizer (P : Set G))
    (h12895 : QuotientKernel U P V₂) :
    ⁅J ⊓ centralizer (P : Set G), W U V₂⁆ ≤ Z P := by
  let C := J ⊓ centralizer (P : Set G)
  have hCH : C ≤ H := relative_centralizer_le H J P A V₂ hH hA hVP
  have hCV : C ≤ centralizer (V₂ : Set G) :=
    inf_le_right.trans (centralizer_le hVP)
  have hCW : C ≤ normalizer (W U V₂ : Set G) :=
    (le_inf (hCH.trans hHU)
      (hCV.trans ((centralizer_le_normalizer _).trans
        (normalizer_le_normalizer_centralizer V₂)))).trans inf_normalizer_le_normalizer_inf
  have hWJ : W U V₂ ≤ J := by
    rw [hJ]
    exact inf_le_right.trans (centralizer_le hB)
  have hWC : W U V₂ ≤ normalizer (C : Set G) :=
    hWJ.trans (relative_centralizer_normalized J P hJP)
  have hcommW : ⁅C, W U V₂⁆ ≤ W U V₂ :=
    le_normalizer_iff_commutator_le_right.mp hCW
  have hcommC : ⁅C, W U V₂⁆ ≤ C :=
    le_normalizer_iff_commutator_le_left.mp hWC
  rw [center_image]
  refine le_inf ?_ (hcommC.trans inf_le_right)
  intro x hx
  have hcx : x ∈ centralizer (P : Set G) := (hcommC hx).2
  exact ((h12895 x (hcommW hx)).mp (by
    intro u hu
    have hc : ⁅x, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcx u hu).symm
    rw [hc]
    exact (Z P).one_mem)).2.1

theorem conjugate_D_le (H U A V₂ : Subgroup G) (g : G)
    (hH : H = centralizer (A : Set G)) (hA : A ≤ V₂)
    (hV : V₂ ≤ conjugate U g) : D H U g ≤ H :=
  relative_centralizer_le H (conjugate H g) (conjugate U g) A V₂ hH hA hV

theorem conjugate_commutator_le (H U A V₂ : Subgroup G) (g : G)
    (hH : H = centralizer (A : Set G)) (hA : A ≤ V₂)
    (hAg : conjugate A g ≤ V₂) (hV : V₂ ≤ conjugate U g)
    (hHU : H ≤ normalizer (U : Set G))
    (hHgUg : conjugate H g ≤ normalizer (conjugate U g : Set G))
    (h12895 : QuotientKernel U (conjugate U g) V₂) :
    ⁅D H U g, W U V₂⁆ ≤ Z (conjugate U g) := by
  apply relative_commutator_le_center H (conjugate H g) U (conjugate U g)
    A (conjugate A g) V₂ hH
  · rw [hH, conjugate_centralizer]
  · exact hA
  · exact hAg
  · exact hV
  · exact hHU
  · exact hHgUg
  · exact h12895
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
variable {G : Type*} [Group G]
theorem centralizer_subgroupOf_map (H U : Subgroup G) (hUH : U ≤ H) :
    (centralizer (U.subgroupOf H : Set H)).map H.subtype =
      H ⊓ centralizer (U : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, ?_⟩
    intro u hu
    exact congrArg Subtype.val (ha ⟨u, hUH hu⟩ hu)
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    intro u hu
    exact Subtype.ext (hxC u hu)

theorem center_subgroupOf_map (H U : Subgroup G) (hUH : U ≤ H) :
    (Z (U.subgroupOf H)).map H.subtype = Z U := by
  rw [center_image, map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hUH, centralizer_subgroupOf_map H U hUH, center_image]
  apply le_antisymm (inf_le_inf_left U inf_le_right)
  exact le_inf inf_le_left (le_inf (inf_le_left.trans hUH) inf_le_right)

theorem conjugate_normalizes (H U : Subgroup G) (g : G)
    (hHU : H ≤ normalizer (U : Set G)) :
    conjugate H g ≤ normalizer (conjugate U g : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [conjugate, conjugate, ← map_commutator]
  exact map_mono (le_normalizer_iff_commutator_le_right.mp hHU)

theorem conjugate_center (U : Subgroup G) (g : G) :
    conjugate (Z U) g = Z (conjugate U g) := by
  rw [center_image, conjugate, map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    centralizer_map, center_image]
  rfl
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
