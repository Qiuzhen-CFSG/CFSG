module

public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ResidualAction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.GL2.FiveWreathSylow

/-!
# Exact orders in the original quintic outer alternative

The actual elementary residual of order twenty-five is self-centralizing
in the two-core quotient. Its Sylow two-subgroup therefore embeds faithfully
in the automorphism group of that residual, whose order divides 480.
The genuine outer action excludes Sylow orders at most eight, leaving
exactly sixteen and thirty-two and quotient orders 400 and 800.
No closure equality, factor-join index or signed coordinates are assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open OddNormalizer
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel

private theorem residual_plane_sylow_orders {K : Type*} [Group K] [Finite K]
    [IsElementaryAbelian 5 (pResidual 2 K)]
    (hcore : pCore 2 K = ⊥) (hR : Nat.card (pResidual 2 K) = 25)
    (hlarge : 200 < Nat.card K) (S : Sylow 2 K) :
    (Nat.card S = 16 ∨ Nat.card S = 32) ∧ Nat.card K = 25 * Nat.card S := by
  let R := pResidual 2 K
  change Nat.card R = 25 at hR
  let α : S →* MulAut R := (MulAut.conjNormal : K →* MulAut R).comp (S : Subgroup K).subtype
  have hdis : Disjoint R (S : Subgroup K) :=
    IsPGroup.disjoint_of_coprime (IsElementaryAbelian.isPGroup 5 R) S.isPGroup' (by decide)
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).mp (by
    apply bot_unique
    intro s hs
    have hc : (s : K) ∈ centralizer (R : Set K) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact hs
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis
      (centralizer_pResidual_le_of_pCore_eq_bot hcore hc) s.property))
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 5) (n := 2) R (by omega)
  have hd : Nat.card S ∣ 480 := by
    have hh := card_dvd_of_injective (f.comp α) (hf.comp hinj)
    rwa [Matrix.GeneralLinearGroup.FiveWreathSylow.generalLinear_card] at hh
  have hnorm : (S : Subgroup K) ≤ normalizer (R : Set K) := by
    rw [normalizer_eq_top]
    exact le_top
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint R (S : Subgroup K) hnorm hdis
  rw [show R ⊔ (S : Subgroup K) = ⊤ from pResidual_sup_sylow_eq_top S,
    card_top, hR] at hprod
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hn6 : n < 6 := by
    by_contra! hn6
    have hh : 64 ∣ 480 := (show 64 ∣ Nat.card S from hn ▸ Nat.pow_dvd_pow 2 hn6).trans hd
    norm_num at hh
  have hn4 : 4 ≤ n := by
    rw [hprod, hn] at hlarge
    by_contra! hh
    interval_cases n <;> norm_num at hlarge
  refine ⟨?_, hprod⟩
  interval_cases n <;> simp_all

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

/-- The original outer alternative has exactly one of two two-core quotient
orders. The calculation applies in both residual-closure branches. -/
theorem source_quintic_outer_exact_quotient_order
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor) :
    Nat.card (J ⧸ pCore 2 J) = 400 ∨ Nat.card (J ⧸ pCore 2 J) = 800 := by
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  obtain ⟨hS, hprod⟩ := residual_plane_sylow_orders (pCore_quotient_pCore_eq_bot 2)
    (source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w)
    (source_quintic_outer_quotient_card hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hker hp)
    ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
  rcases hS with hS | hS
  · exact Or.inl (by simpa only [hS] using hprod)
  · exact Or.inr (by simpa only [hS] using hprod)

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
