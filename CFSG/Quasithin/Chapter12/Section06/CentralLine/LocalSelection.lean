module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalSource
public import CFSG.Quasithin.Chapter2.Source
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.Mathieu.M11.Properties.Order
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Selecting the original escaping local subgroup in 12.6.23

The literal A₈ action quotient makes 20160 divide |G|. A nonzero vector in
C_V(L) has nonsolvable centralizer since it contains L. These facts exclude
all models in the unique maximal-two-local theorem: the Bender models have
solvable proper Sylow overgroups, odd linear rank-one models have solvable
involution centralizers, and the two small models fail the order divisibility.
Thus an actual maximal two-local escapes M=N_G(L). Finite minimization
constructs the original H-star member, and the proved weak-closure argument
selects the same conjugate of V inside full Q with nontrivial local image.

This supplies the previously explicit H-star existence premise. Compatible
five-point markings and their evenness remain local source obligations; no
fixed-space vanishing or equality C_J(V_H)=O₂(J) is assumed or asserted.
Source: Aschbacher–Smith, 12.6.23, printed pp.829–830, with 2.1.1, p.518.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine.LocalContradiction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The actual orthogonal action quotient contributes its order to the ambient group. -/
theorem OrthogonalMarking.alternating_eight_order_dvd
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) :
    20160 ∣ Nat.card G := by
  have hc : Nat.card (L ⧸ (conjugation L V hn).ker) = 20160 := by
    rw [Nat.card_congr D.groupEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [← hc]
  exact (card_dvd_of_surjective (QuotientGroup.mk' (conjugation L V hn).ker)
    (QuotientGroup.mk'_surjective _)).trans L.card_subgroup_dvd_card

/-- A nonzero original fixed vector excludes every unique-overgroup model. -/
theorem SourceHypothesis.fixed_not_unique_overgroup_model
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hz : ZV L V ≠ ⊥) :
    ¬ ClassificationModels.IsTheorem211Model G := by
  have hLns : ¬ Group.IsSolvable L :=
    Chapter1.mem_L_not_isSolvable H.source.maximal_faithful.1.1
  have hcard := D.alternating_eight_order_dvd
  intro hm
  cases hm with
  | bender hb =>
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      H.source.simpleQTKE T H.source.maximal_faithful.1
    have horbit : componentOrbit L (T : Subgroup G) = L := by
      exact le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
        H.chosen.sylow_normalizes_component) (le_componentOrbit L T)
    have hproper : M L ≠ ⊤ := by
      simpa only [horbit, M] using hu.normalizer_proper
    let : Group.IsSolvable (normalizer (L : Set G)) :=
      ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup
      hb T (M L) H.chosen.sylow_normalizes_component hproper
    exact hLns (Group.isSolvable_of_isSolvable_injective
      (f := inclusion L.le_normalizer) (inclusion_injective L.le_normalizer))
  | linear_prime p hp hlarge iso =>
    obtain ⟨z,hzV,hzne⟩ := (ZV L V).bot_or_exists_ne_one.resolve_left hz
    have hz2 : orderOf z = 2 := orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian z hzV.1, hzne⟩
    have hLC : L ≤ centralizer ({z} : Set G) := by
      intro l hl
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hzV.2 l hl
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p, 1, hp.1, hp.1.odd_of_ne_two (by omega), by omega, by simpa using hF⟩
    have hze : GorensteinWalter.IsInvolution (e z) := by
      have he := (e.orderOf_eq z).trans hz2
      exact ⟨fun h => by simp [h] at he,
        by simpa only [he] using pow_orderOf_eq_one (e z)⟩
    let := Theory.PSL2.involution_centralizer_isSolvable ho (e z) hze
    let c := CentralizerSmallKernelTransport.centralizerEquiv e z
    let := Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
    exact hLns (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hLC) (inclusion_injective hLC))
  | linear_three iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let := Fintype.ofFinite F
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

/-- The original fixed-space branch has an actual escaping maximal two-local. -/
theorem SourceHypothesis.fixed_hasMaximalOutside
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hz : ZV L V ≠ ⊥) :
    Chapter3.HasMaximalOutside T (M L) := by
  have hmax : IsMaximalTwoLocal (M L) := (H.chosen.doubledNormalizer_unique H.source).1
  have hTM : (T : Subgroup G) ≤ M L := H.chosen.sylow_normalizes_component
  by_contra hout
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M L := by
    intro N hN hTN
    apply hN.eq_of_le hmax.1
    by_contra hNM
    have hneq : N ≠ M L := fun he => hNM (he ▸ le_rfl)
    exact hout (Chapter3.hasMaximalOutside_of_two_distinct hmax hN hTM hTN hneq)
  exact H.fixed_not_unique_overgroup_model D hz
    (Chapter2.theorem_2_1_1 H.source.simpleQTKE T (M L) hmax hTM hunique)

/-- Finite minimization now supplies the H-star member used by 12.6.23. -/
theorem SourceHypothesis.fixed_exists_hstar
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hz : ZV L V ≠ ⊥) :
    ∃ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) (M L) :=
  Chapter3.exists_HStar_of_hasMaximalOutside (H.fixed_hasMaximalOutside D hz)

/-- Selection and weak closure produce a nonsolvable local group and the
same actual conjugate of V inside the full original Q, with nontrivial image. -/
theorem SourceHypothesis.fixed_exists_hstar_actor
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) (M L) ∧
      ¬ Group.IsSolvable J ∧ ∃ g : G,
        V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
        V.map (MulAut.conj g).toMonoidHom ≤ Q T L ∧
        localImage T J (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  obtain ⟨J,hJ⟩ := H.fixed_exists_hstar D hz
  exact ⟨J,hJ,H.fixed_hstar_not_solvable D hTV hTI hz hJ,
    H.fixed_exists_nontrivial_local_actor D hTV hTI hz hJ⟩

end CFSG.Quasithin.Chapter12.Section06
