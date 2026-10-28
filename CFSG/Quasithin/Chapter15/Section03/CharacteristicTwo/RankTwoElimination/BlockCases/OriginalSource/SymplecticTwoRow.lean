module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSixStarCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankTwoCoreCenterAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticTwoActor
public import Theory.Alternating.TripleSixActorInversion
/-!
# Excluding the actual binary symplectic source row

The star component is A6. Its ordinary core cover is excluded by the
source Sylow overgroup and three-rank. For the triple cover, Yplus lies
in the component and contains its cubic center modulo the two-core.
Consequently the actual join LR fixes this center. The marked Sp4(2)
actor supplies a transposition on A6; its lift inverts that same center,
a contradiction. The argument retains the genuine odd kernel possibility.

The consumer uses the original selected local data and the literal marked
moved section, with no block, cover, Sylow, or kernel premise added.
Source: Aschbacher–Smith C.2.7 and 15.3.17–21, printed pp.145–147,1126–1127;
GLS3 5.2.3 and 5.2.7 for the triple-cover action.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
include hG hempty hM hu hmany hI htwo hf

theorem source_15_3_21_symplecticTwo_row :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (H : Subgroup J),
      MarkedActionEquiv s.action H (C.subgroupOf J)
        (symplecticNatural (k := ZMod 2) 2) (commutator (Sp (ZMod 2))) → False := by
  intro C J hCJ s H e
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  let δ := Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)
  let b : C ≃* alternatingGroup (Fin 6) :=
    ((subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv).trans δ
  rcases coreToStar_alternatingSix_alternatives d c h.normalizes b with hOrd | ⟨hk,hTri⟩
  · obtain ⟨eq⟩ := hOrd
    obtain ⟨P,hP⟩ := h11.sylow
    have hYL := yplus_le_of_alternatingSix_quotient d c h11.theta_eq.symm hrI eq
    exact no_alternatingSix_quotient d c P hP h11.theta_eq.symm
      (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) hYL eq
  · obtain ⟨eq⟩ := hTri
    let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
    have hYL := yplus_le_of_hexacode_quotient d c h11.theta_eq.symm hrI eq
    have hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3 :=
      (Nat.card_congr (centerCongr eq).toEquiv).trans Representation.Hexacode.even_center_card
    let f : Covering (c.L ⧸ pCore 2 c.L) (alternatingGroup (Fin 6)) := {
      toMonoidHom := b.toMonoidHom.comp (coreToStar h.normalizes)
      surjective := b.surjective.comp (coreToStar_surjective h.normalizes) }
    have hker : Nat.card f.toMonoidHom.ker = 3 := by
      change Nat.card (b.toMonoidHom.comp (coreToStar h.normalizes)).ker = 3
      rw [MonoidHom.ker_comp_of_injective _ _ b.injective]
      exact hk
    obtain ⟨r,hr,hcompat⟩ := ChapterC.C27Source.symplecticTwo_core_swap_actor
      c.L d.R h.normalizes hCJ s H e
    let β := permutationAction (Equiv.swap (0 : Fin 6) 1)
    have hout : ∀ g : alternatingGroup (Fin 6), β ≠ MulAut.conj g := by
      intro g hg
      have he : Equiv.swap (0 : Fin 6) 1 = (g : Equiv.Perm (Fin 6)) :=
        permutationAction_injective (hg.trans (permutationAction_coe g).symm)
      have hs := Equiv.Perm.mem_alternatingGroup.mp g.property
      rw [← he,Equiv.Perm.sign_swap (by decide)] at hs
      exact (by decide : (-1 : ℤˣ) ≠ 1) hs
    have hβ : orderOf β = 2 := by
      apply orderOf_eq_prime
      · change permutationAction (Equiv.swap (0 : Fin 6) 1) ^ 2 = 1
        rw [← map_pow,pow_two,Equiv.swap_mul_self,map_one]
      · intro he
        exact hout 1 (he.trans (map_one MulAut.conj).symm)
    let a := quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r)
    have hcomp : ∀ k, f (a k) = β (f k) := hcompat
    let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isQuasisimple
    let fHex : Covering Atlas.Codes.HexEvenAutomorphisms (alternatingGroup (Fin 6)) := {
      toMonoidHom := f.toMonoidHom.comp eq.symm.toMonoidHom
      surjective := f.surjective.comp eq.symm.surjective }
    have hkHex : Nat.card fHex.toMonoidHom.ker = 3 := by
      change Nat.card (f.toMonoidHom.comp eq.symm.toMonoidHom).ker = 3
      rw [MulEquiv.toMonoidHom_eq_coe,MonoidHom.ker_comp_mulEquiv,
        card_map_of_injective eq.injective]
      exact hker
    let aHex := MulAut.congr eq a
    have hcHex : ∀ k, fHex (aHex k) = β (fHex k) := by
      intro k
      change f (eq.symm (eq (a (eq.symm k)))) = β (f (eq.symm k))
      rw [eq.symm_apply_apply,hcomp]
    have hiHex := GLS3.Chapter5.TripleSixActorInversion.center_inverted_of_noninner_quotient
      fHex hkHex aHex β hcHex hβ hout
    have hinv (z : c.L ⧸ pCore 2 c.L) (hz : z ∈ center (c.L ⧸ pCore 2 c.L)) :
        a z = z⁻¹ := by
      have he := hiHex (eq z) (centerCongr eq ⟨z,hz⟩).property
      apply eq.injective
      change eq (a (eq.symm (eq z))) = (eq z)⁻¹ at he
      simpa only [eq.symm_apply_apply,map_inv] using he
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (c.L ⧸ pCore 2 c.L)) 3
      (by rw [hc])
    have hfix := source_rankTwo_join_fixes_core_center hG d hI htwo c hYL hc
      h.normalizes r hr (z : c.L ⧸ pCore 2 c.L) z.property
    have hpow : (z : c.L ⧸ pCore 2 c.L) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (z : c.L ⧸ pCore 2 c.L) * z = (z : c.L ⧸ pCore 2 c.L)⁻¹ * z :=
          congrArg (fun t => t * (z : c.L ⧸ pCore 2 c.L))
            (hfix.symm.trans (hinv (z : c.L ⧸ pCore 2 c.L) z.property))
        _ = 1 := inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hpow
    rw [Subgroup.orderOf_coe,hz] at hd
    norm_num at hd
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
