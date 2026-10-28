module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticFaithfulAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticPermuting
public import Theory.GroupTheory.PermutingSubgroupIntersection

/-!
# The original quintic product in the actual component stabilizer

The comparison group's component stabilizer is normal of index at most
two. Its intersection with the supplied T is therefore an actual Sylow.
The original order-five subgroup remains in that stabilizer, and both
of its products with this same Sylow are the literal intersection of XT
with the stabilizer. This supplies the marked product for the quotient
component action without replacing T by an arbitrary Sylow.

Source: Aschbacher--Smith 6.1.4 and 1.2.1(3), printed pp.665 and 504.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual component stabilizer retains the original Sylow intersection
and a literal permuting quintic subgroup. -/
theorem original_hermitian_quintic_component_stabilizer_product
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (K : Set G))
      (M₁ ⊓ normalizer (K : Set G)) ∧
    ∃ D : Subgroup G, Nat.card D = 5 ∧ D ≤ quinticResidual T L ∧
      D ≤ M₁ ⊓ normalizer (K : Set G) ∧
      (D : Set G) * (((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) =
        (((quinticResidual T L ⊔ (T : Subgroup G)) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) ∧
      (((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) * (D : Set G) =
        (((quinticResidual T L ⊔ (T : Subgroup G)) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) := by
  have hTM : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hq := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE
    (Chapter1.mem_H_of_isTwoLocal hM₁.1)
  let N := M₁ ⊓ normalizer (K : Set G)
  have hN : (N.subgroupOf M₁).Normal := by
    have he : N.subgroupOf M₁ = normalizer (K.subgroupOf M₁ : Set M₁) := by
      change (M₁ ⊓ normalizer (K : Set G)).comap M₁.subtype = _
      rw [comap_inf]
      change (M₁.subgroupOf M₁) ⊓ (normalizer (K : Set G)).subgroupOf M₁ = _
      rw [subgroupOf_self,top_inf_eq]
      exact subgroupOf_normalizer_eq hK.1
    rw [he]
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hq hK.2 with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      infer_instance
    · exact (normalizer (K.subgroupOf M₁ : Set M₁)).normal_of_index_eq_two hi
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]⟩
  have hSN := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (show N ≤ M₁ from inf_le_left) hN.isSubnormal
  have hinf : (T : Subgroup G) ⊓ N = (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [show N = M₁ ⊓ normalizer (K : Set G) from rfl,←inf_assoc,inf_eq_left.mpr hTM]
  rw [hinf] at hSN
  refine ⟨hSN,?_⟩
  obtain ⟨D,hD,hDX,hDT,hTD⟩ := original_hermitian_quintic_permuting_torus h hout hm
  have hDN : D ≤ normalizer (K : Set G) := hDX.trans
    (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)
  have hXM : quinticResidual T L ≤ M₁ := by
    obtain ⟨E,_,_,_,_,_,hXT⟩ := original_hermitian_quintic_torus h hout hm
    exact le_sup_left.trans (hXT.trans hCM₁)
  obtain ⟨ha,hb⟩ := set_products_intersection_of_left_le D (T : Subgroup G)
    (normalizer (K : Set G)) hDN
  change (D : Set G) * ((T : Subgroup G) : Set G) =
    ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) at hDT
  change ((T : Subgroup G) : Set G) * (D : Set G) =
    ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) at hTD
  rw [hDT] at ha
  rw [hTD] at hb
  exact ⟨D,hD,hDX,le_inf (hDX.trans hXM) hDN,ha,hb⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
