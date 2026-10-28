module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.Assembly
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Setup
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import CFSG.Quasithin.Chapter2.Source
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.Mathieu.M11.Properties.Order
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

@[expose] public section
open Subgroup Theory.GroupTheory
set_option linter.style.haveILetI false
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem not_model_of_local_centralizer
    (T : Sylow 2 G) (L M : Subgroup G)
    (hL : ¬ Group.IsSolvable L) (hLM : L ≤ M)
    (hTM : (T : Subgroup G) ≤ M) (hM : M ≠ ⊤)
    (z : G) (hz : orderOf z = 2) (hMz : M = centralizer ({z} : Set G))
    (hcard : 168 ∣ Nat.card G) : ¬ ClassificationModels.IsTheorem211Model G := by
  intro hm
  have hMns : ¬ Group.IsSolvable M := by
    intro hs
    letI := hs
    exact hL (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hLM) (inclusion_injective hLM))
  cases hm with
  | bender hb =>
    exact hMns (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup
      hb T M hTM hM)
  | linear_prime p hp hlarge iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p, 1, hp.1, hp.1.odd_of_ne_two (by omega), by omega, by simpa using hF⟩
    have hze : GorensteinWalter.IsInvolution (e z) := by
      have he := (e.orderOf_eq z).trans hz
      exact ⟨fun h => by simp [h] at he,
        by simpa only [he] using pow_orderOf_eq_one (e z)⟩
    letI := Theory.PSL2.involution_centralizer_isSolvable ho (e z) hze
    let c := CentralizerSmallKernelTransport.centralizerEquiv e z
    apply hMns
    rw [hMz]
    exact Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
  | linear_three iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    letI := Fintype.ofFinite F
    let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    have hc : Nat.card G = 5616 :=
      (Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv).trans
        Matrix.PSL3Three.card_PSL
    rw [hc] at hcard
    norm_num at hcard
  | mathieu_eleven iso =>
    obtain ⟨e⟩ := iso
    have hc : Nat.card G = 7920 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
    rw [hc] at hcard
    norm_num at hcard

theorem hasMaximalOutside_slThree
    {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    Chapter3.HasMaximalOutside T (normalizer (L : Set G)) := by
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  obtain ⟨z, hz, _, hMz, _⟩ := fixed_involution_setup_of_card_two h D structural
    (E.fixed_card_eq_two hne)
  have hTL := (structural G T L h).1
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  have hproper : normalizer (L : Set G) ≠ ⊤ := by
    simpa only [horbit] using hu.normalizer_proper
  have hLns : ¬ Group.IsSolvable L :=
    Chapter1.mem_L_not_isSolvable h.maximal_faithful.1.1
  have hcard : 168 ∣ Nat.card G := by
    have hc : Nat.card (L ⧸ pCore 2 L) = 168 :=
      (Nat.card_congr E.quotientEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
    rw [← hc]
    exact (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)).trans L.card_subgroup_dvd_card
  by_contra hout
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hTN
    apply hN.eq_of_le hmax.1
    by_contra hNM
    have hneq : N ≠ normalizer (L : Set G) := by
      intro heq
      apply hNM
      simp [heq]
    exact hout (Chapter3.hasMaximalOutside_of_two_distinct hmax hN hTL hTN hneq)
  exact not_model_of_local_centralizer T L (normalizer (L : Set G)) hLns
    L.le_normalizer hTL hproper z hz hMz hcard
    (Chapter2.theorem_2_1_1 h.simpleQTKE T _ hmax hTL hunique)

theorem localSelectionSource
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    LocalSelectionSource.{u} := by
  intro X _ _ T L V h D hmodel hne _hZ _hs
  exact Chapter3.exists_HStar_of_hasMaximalOutside
    (hasMaximalOutside_slThree h D structural marked hmodel hne)

theorem noncommutingConjugate1241_of_parameter_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (parameters : LocalParameterSource.{u}) : NoncommutingConjugate1241.{u} :=
  noncommutingConjugate1241_of_local_sources structural
    (localSelectionSource structural marked) parameters

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
