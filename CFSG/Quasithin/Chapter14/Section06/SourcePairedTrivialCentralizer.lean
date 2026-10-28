module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedEndgameAssembly
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCenterBound
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCoreQuotient
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedEndgameGeometry

/-!
# The paired source contradiction after the residual centralizer is trivial

The original paired configuration supplies both irreducible sections, the
center bound and all five point-core identities. The same-conjugator
intersection of order 16 forces the residual core into the quotient omega
preimage; the centralizer sandwich then identifies the full point core with
the two residual factors and gives the original normalizer contradiction.

This discharges every geometric premise of the source endgame under D = 1.
The separate centralizer-normalizer argument supplies D = 1 in the full
characteristic-two factorization proof.

Source: Aschbacher--Smith 14.6.9(k)--(n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The original paired A₅ configuration is impossible when its residual
centralizer in the Sylow intersection is trivial. -/
theorem source_paired_exclusion_of_trivial_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) (hΛT : Λ ≤ (T : Subgroup G))
    (hD : ((T : Subgroup G) ⊓ I) ⊓
      centralizer (((pResidual 2 I).map I.subtype : Subgroup G) : Set G) = ⊥) : False := by
  obtain ⟨hZ₀,hsmall,hcomm,hcent,hmod⟩ := source_paired_endgame_geometry
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hpairIndex hD
  obtain ⟨hZn,hcenter⟩ := source_paired_quotient_center_bound
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hD
  let := hZn
  have hirr := source_paired_core_quotient_irreducible
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hpairIndex hD
  obtain ⟨_,_,_,_,_,hcore,_⟩ := c.alternating_pair_family b i j hij hs hi hpairIndex
  rw [hD,sup_bot_eq] at hcore
  rw [hcore] at hirr
  apply source_paired_exclusion_of_endgame_geometry hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex hΛT
    hZ₀ _ hirr hsmall hcomm hcent hmod
  exact (quotient_center_preimage_le_iff _ _ _).mp hcenter
end CFSG.Quasithin.Chapter14.Section06
