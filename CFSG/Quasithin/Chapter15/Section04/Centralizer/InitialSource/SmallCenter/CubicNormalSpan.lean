module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.FixedPairAmbient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit

/-!
# The original normal cubic orbit and its concrete models

The actual alternating-three block produced by failure of the one fixed
characteristic pair has at most two conjugates in M. Its normal Sylow orbit
therefore is A₄ or A₄ × A₄. The original Thompson movement passes to
that orbit, and it still generates M with the original Sylow subgroup.
All rank, characteristic-two and block inputs come from the original
Chapter15 member, rather than a recognition certificate.

Source: Aschbacher--Smith 15.4.7, printed p.1158, using C.1.28.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The same actual cubic orbit is normal, moved, generating, and has its concrete model. -/
theorem member_cubic_normal_span {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (R : Subgroup M) (hb : ChapterC.IsBlock R) (ha : ChapterC.IsAlternatingBlock R 3)
    (hm : R = ⁅R,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆)
    (hgen : R ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤) :
    let N := conjugateSpanBy R (T.subtype h.sylow_le : Subgroup M)
    N.Normal ∧ N = ⁅N,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆ ∧
    N ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ ∧
    (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨ Nonempty (N ≃* AlternatingFourPair.Model)) := by
  let S := T.subtype h.sylow_le
  have hfit : generalizedFitting M = pCore 2 M :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  have hr : primeRank 3 M ≤ 2 :=
    (h.ambient.twoLocal_sqtk h.maximal.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  obtain ⟨hn,hmodels⟩ := ChapterC.RankOne.ChiProduct.cubic_orbit_models hfit hr S R hb ha
  refine ⟨hn,?_,?_,hmodels⟩
  · exact (commutator_conjugateSpanBy_eq_self R (S : Subgroup M)
      (elementaryAbelianMaxJ (S : Subgroup M)) (sSup_le fun _ hA => hA.1)
      ((S : Subgroup M).le_normalizer.trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _)) hm.symm).symm
  · apply top_unique
    rw [←hgen]
    exact sup_le_sup_right (le_conjugateSpanBy R _) _

/-- The raw source setup constructs the normal A₄ or A₄-pair orbit. -/
theorem source_fixed_pair_normal_models
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    ∃ (M X : Subgroup G) (s : ℕ) (h : Input KnownSimple.IsKnownSimple T M X s)
      (K : Subgroup M),
      let N := conjugateSpanBy ((pResidual 2 K).map K.subtype) (T.subtype h.sylow_le : Subgroup M)
      N.Normal ∧ N = ⁅N,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆ ∧
      N ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ ∧
      (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨ Nonempty (N ≃* AlternatingFourPair.Model)) := by
  obtain ⟨M,X,s,h,K,hb,ha,hm,hgen⟩ :=
    source_fixed_pair_ambient_block hA hC h311 hB hG T hempty hmany hZ D hD
  exact ⟨M,X,s,h,K,member_cubic_normal_span h _ hb ha hm hgen⟩
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
