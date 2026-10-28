module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary displacements of an outer Sylow involution

An elementary actor normal in a Sylow subgroup induces elementary
displacements on the Sylow intersection with any normal subgroup. The
construction retains the actual conjugation automorphism and that intrinsic
Sylow. This packages the inputs to the linear-group step in
Aschbacher--Smith G.10.15(3), using G.10.9(2), printed pp.360,363.

No impossibility assertion is made: degree four admits such outer actions
via a transposition of S8 on A8. Applications must retain the additional
representation hypotheses needed to exclude that exceptional case.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- An outer involution normalizing a Sylow subgroup, with all of its
Sylow displacements contained in an elementary subgroup of that Sylow. -/
structure ElementaryOuterSylowAction (H : Type*) [Group H] where
  sylow : Sylow 2 H
  automorphism : MulAut H
  square : automorphism ^ 2 = 1
  outer : automorphism ∉ MulAut.innerSubgroup H
  preserves : ∀ u ∈ (sylow : Subgroup H), automorphism u ∈ (sylow : Subgroup H)
  displacementGroup : Subgroup H
  elementary : IsElementaryAbelian 2 displacementGroup
  contained : displacementGroup ≤ (sylow : Subgroup H)
  displacement : ∀ u ∈ (sylow : Subgroup H),
    automorphism u * u⁻¹ ∈ displacementGroup

namespace ElementaryOuterSylowAction
variable {D : Type*} [Group D] [Finite D]

/-- Restrict the actual Sylow to a normal subgroup. Normality of the
original elementary actor puts every displacement in its Sylow intersection. -/
def of_normal_elementary (H : Subgroup D) [H.Normal]
    (S : Sylow 2 D) (X : Subgroup D) [IsElementaryAbelian 2 X]
    (hXS : X ≤ (S : Subgroup D)) (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
    (x : X) (ho : (MulAut.conjNormal (x : D) : MulAut H) ∉ MulAut.innerSubgroup H) :
    ElementaryOuterSylowAction H := by
  let P := Classical.choose (S.exists_subgroupOf_eq_of_normal H)
  have hP := Classical.choose_spec (S.exists_subgroupOf_eq_of_normal H)
  let C := ⁅X,(S : Subgroup D) ⊓ H⁆
  have hCX : C ≤ X :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hSX)
  have hCH : C ≤ H :=
    (commutator_mono le_rfl inf_le_right).trans (commutator_le_right _ _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCX) (inclusion_injective hCX)
  refine ⟨P, MulAut.conjNormal (x : D), ?_, ho, ?_, C.subgroupOf H,
    IsElementaryAbelian.subgroupOf hCH, ?_, ?_⟩
  · rw [← map_pow]
    have hx : (x : D) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : D) x.property
    rw [hx, map_one]
  · intro u hu
    rw [hP] at hu ⊢
    change (x : D) * (u : D) * (x : D)⁻¹ ∈ (S : Subgroup D)
    exact (S : Subgroup D).mul_mem ((S : Subgroup D).mul_mem (hXS x.property) hu)
      ((S : Subgroup D).inv_mem (hXS x.property))
  · intro u hu
    rw [hP]
    exact hXS (hCX hu)
  · intro u hu
    rw [hP] at hu
    change (x : D) * (u : D) * (x : D)⁻¹ * (u : D)⁻¹ ∈ C
    exact commutator_mem_commutator x.property ⟨hu,u.property⟩
end ElementaryOuterSylowAction
end Theory.GroupTheory
