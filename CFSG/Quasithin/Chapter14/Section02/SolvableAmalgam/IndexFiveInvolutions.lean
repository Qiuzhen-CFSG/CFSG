module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import Theory.SpecificGroups.QuinticInvolutionCommutator

/-!
# Involution commutators in the original index-five quotient

The actual quotient H/O₂(H) in the original index-five branch is D₁₀ or
Sz(2). The finite-model witness therefore lifts to an element of the literal
subgroup H whose commutator with the specified involution image has order
five in that same quotient. This discharges the model input in the
critical-core escape argument of Aschbacher--Smith 14.6.12.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource
  ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Every original quotient involution has an order-five commutator, lifted in H. -/
theorem source_index_five_involution_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hi : (T : Subgroup G).relIndex H = 5)
    (t : H) (ht : orderOf (QuotientGroup.mk' (pCore 2 H) t) = 2) :
    ∃ x : H, orderOf (QuotientGroup.mk' (pCore 2 H) (t * x * t⁻¹ * x⁻¹)) = 5 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨x,hx⟩ := Theory.SpecificGroups.exists_order_five_commutator_of_quintic_model
    (source_index_five_models hG T hempty hM hu hmany hcard e H hH hi) (q t) ht
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  refine ⟨y,?_⟩
  simpa only [map_mul,map_inv] using hx

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
