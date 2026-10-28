module

public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.OuterOrders
public import Theory.ElementaryAbelian.FivePlaneLargeTwoScalar

/-!
# Simultaneous squaring on the original quintic residual

The exact original quotient orders force the faithful Sylow action on its
residual plane to have order sixteen or thirty-two. Every such two-group
contains the central squaring scalar. Lift its actual preimage to the
prescribed Sylow subgroup, preserving the original quotient and residual.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam OddNormalizer
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs w

/-- In either closure branch, an actual member of the original Sylow
simultaneously squares every element of the original residual plane. -/
theorem source_quintic_outer_simultaneous_squaring
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor) :
    ∃ s : J, (s : G) ∈ T ∧ ∀ r : pResidual 2 (J ⧸ pCore 2 J),
      QuotientGroup.mk' (pCore 2 J) s * r * (QuotientGroup.mk' (pCore 2 J) s)⁻¹ =
        (r : J ⧸ pCore 2 J) ^ 2 := by
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  let K := J ⧸ pCore 2 J
  let R := pResidual 2 K
  let S := (T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hR : Nat.card R = 25 := source_quintic_residual_plane_card
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w
  have hdis : Disjoint R (S : Subgroup K) := IsPGroup.disjoint_of_coprime
    (IsElementaryAbelian.isPGroup 5 R) S.isPGroup' (by decide)
  have hnorm : (S : Subgroup K) ≤ normalizer (R : Set K) := by
    rw [normalizer_eq_top]
    exact le_top
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint R (S : Subgroup K) hnorm hdis
  rw [show R ⊔ (S : Subgroup K) = ⊤ from pResidual_sup_sylow_eq_top S,card_top,hR] at hprod
  change Nat.card K = 25 * Nat.card S at hprod
  have hSc : Nat.card S = 16 ∨ Nat.card S = 32 := by
    have hc := source_quintic_outer_exact_quotient_order
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hker hp
    change Nat.card K = 400 ∨ Nat.card K = 800 at hc
    omega
  let α : S →* MulAut R := (MulAut.conjNormal : K →* MulAut R).comp (S : Subgroup K).subtype
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).mp (by
    apply bot_unique
    intro s hs
    have hc : (s : K) ∈ centralizer (R : Set K) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact hs
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis
      (centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2) hc) s.property))
  have hα : Nat.card α.range = 16 ∨ Nat.card α.range = 32 := by
    rwa [←Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  obtain ⟨β,⟨s,rfl⟩,hβ⟩ := IsElementaryAbelian.FivePlaneLargeTwoScalar.exists_squaring
    hR α.range (S.isPGroup'.of_surjective α.rangeRestrict α.rangeRestrict_surjective) hα
  obtain ⟨x,hxT,hxs⟩ := s.property
  refine ⟨x,hxT,fun r => ?_⟩
  have hh := congrArg Subtype.val (hβ r)
  change (s : K) * (r : K) * (s : K)⁻¹ = (r : K) ^ 2 at hh
  rwa [←hxs] at hh

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
