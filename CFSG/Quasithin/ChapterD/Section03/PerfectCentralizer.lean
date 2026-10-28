module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import Theory.Representation.BinaryOffender.NormalClosure
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerPrime
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiExchange
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit

/-!
# Starred actors on a normal perfect subgroup

A starred cubic actor cannot meet a three-free perfect-subgroup centralizer.
If it did, D.2.13 makes it centralize every odd prime core: the only remaining
prime five forces actor rank one, excluded by perfect full-module movement.
Trivial two-core then produces a moved component of the centralizer. The
actual SQTK cover identifies it as Suzuki. Its normalized and exchanged
orbits contradict the existing strict-ratio and displacement bounds.

Unlike the single-component version of D.3.9, this argument applies to a
normal perfect product. The Chapter10 quiet-seed consumer uses precisely
the original component-square image, with its full centralizer kernel.
Source: Aschbacher--Smith D.2.13, D.3.9 and D.3.21,
printed pp.184--185,200--201,204--207 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
open Chapter3.Section02.ChosenSource325
universe u v
variable {H : Type u} {V : Type v} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V)

private theorem semisimple_sqtk
    (c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple H)
    (J : Subgroup H) (hJ : ChapterA.Section02.IsSemisimple J) :
    IsSQTK KnownSimple.IsKnownSimple J := by
  let q := c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel)
  have hq : Function.Surjective q := c.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : ChapterA.Section02.IsSectionOf J c.Cover :=
    (ChapterA.Section02.IsSectionOf.subgroup J).ambient_surjective q hq
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple c.sqtk.stronglyQuasithin c.sqtk.isKGroup hs hJ,
    hs.isKGroup c.sqtk.isKGroup⟩

private theorem component_sqtk
    (c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple H)
    (J : Subgroup H) (hJ : IsComponent H J) : IsSQTK KnownSimple.IsKnownSimple J := by
  let := hJ.2
  apply semisimple_sqtk c J
  apply top_unique
  exact le_sSup (show IsComponent J ⊤ from
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩)

private theorem three_free_component_suzuki
    (c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple H)
    (hcore : pCore 2 H = ⊥)
    (J : Subgroup H) (hJ : IsComponent H J) (h3 : Nat.Coprime 3 (Nat.card J)) :
    ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  let := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,hcore]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have htop : IsComponent J ⊤ :=
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩
  have hclass := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    J (component_sqtk c J hJ) hJ2 ⊤ htop.isCComponent
  have h3top : Nat.Coprime 3 (Nat.card (⊤ : Subgroup J)) := by
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup J) ≃* J).toEquiv] using h3
  obtain ⟨r,hr,⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.a36_suzuki_of_coprime
      hclass h3top
  exact ⟨r,by omega,⟨(topEquiv : (⊤ : Subgroup J) ≃* J).symm.trans e⟩⟩

/-- A starred actor is faithful on a normal perfect subgroup with zero fixed
space and three-free centralizer in an actual SQTK quotient. -/
theorem starred_inf_perfect_centralizer_eq_bot
    (hf : Function.Injective ρ) (hcore : pCore 2 H = ⊥)
    (c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple H)
    (K : Subgroup H) [K.Normal] [Group.IsPerfect K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤) (hfix : fixedSpace ρ K = ⊥)
    (h3 : Nat.Coprime 3 (Nat.card (centralizer (K : Set H))))
    {A : Subgroup H} (hA : A ∈ QhatStar ρ) :
    A ⊓ centralizer (K : Set H) = ⊥ := by
  classical
  by_contra hBn
  let C := centralizer (K : Set H)
  let B := A ⊓ C
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hCcore : pCore 2 C = ⊥ := normal_subgroup_twoCore_eq_bot C hcore
  have hmap (p : ℕ) : (pCore p C).map C.subtype ≤ pCore p H :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
  have hfit : (fittingSubgroup C).map C.subtype ≤ centralizer (A : Set H) := by
    rw [fitting_eq_sup_pCore,Subgroup.map_iSup]
    apply iSup_le
    intro p
    have hp : p.1.1.Prime := Fact.out
    by_cases hp2 : p.1.1 = 2
    · rw [hp2,hCcore,Subgroup.map_bot]
      exact bot_le
    by_cases hp3 : p.1.1 = 3
    · have hz : pCore 3 C = ⊥ := by
        apply (eq_bot_iff_card _).mpr
        obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := C)).exists_card_eq
        have hd := (pCore 3 C).card_subgroup_dvd_card
        rw [hn] at hd ⊢
        exact Nat.eq_one_of_dvd_coprimes (h3.pow_left n) dvd_rfl hd
      rw [hp3,hz,Subgroup.map_bot]
      exact bot_le
    have hc : pCore p.1.1 H ≤ centralizer (A : Set H) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      by_contra hm
      have hh := source_lemma_D_2_13_one_two ρ hf hA (hp.odd_of_ne_two hp2) hm
      have hp5 := hh.1.resolve_left hp3
      exact hBn (rank_one_starred_component_centralizer_eq_bot ρ hf K hfull hA
        (hh.2 hp5).2.1)
    exact (hmap p.1.1).trans hc
  have hBfit : B.subgroupOf C ≤ centralizer (fittingSubgroup C : Set C) := by
    intro b hb f hf'
    exact C.subtype_injective ((hfit (mem_map_of_mem C.subtype hf') b hb.1).symm)
  have hBne : B.subgroupOf C ≠ ⊥ := by
    intro hz
    apply hBn
    have hh := congrArg (map C.subtype) hz
    simpa only [map_subgroupOf_eq_of_le (show B ≤ C from inf_le_right),Subgroup.map_bot] using hh
  obtain ⟨J,hJ,hm⟩ := exists_component_moved_of_centralizes_fitting 2 (B.subgroupOf C)
    (((IsElementaryAbelian.isPGroup 2 A).to_le (show B ≤ A from inf_le_left)).comap_subtype)
    hBne hCcore hBfit
  let J' := J.map C.subtype
  let := hJ.2
  have hJ' : IsComponent H J' :=
    ⟨hJ.1.trans' (inferInstance : C.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (J.equivMapOfInjective C.subtype C.subtype_injective)⟩
  have hJC : J' ≤ C := map_subtype_le J
  have hm' : ⁅J',B⁆ ≠ ⊥ := by
    intro hz
    apply hm
    apply (map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le (show B ≤ C from inf_le_right)]
    exact hz
  obtain ⟨r,hr,⟨eJ⟩⟩ := three_free_component_suzuki c hcore J' hJ'
    (h3.of_dvd_right (card_dvd_of_le hJC))
  let := hJ'.2
  have hnot : ¬ A ≤ normalizer (J' : Set H) := by
    intro hn
    exact no_normalized_suzuki_support ρ hf K J' A B hfix hJC
      (component_sqtk c J' hJ') hJ'.isCComponent.ne_bot hn hA inf_le_left
      (hJ'.commutator_eq_self_of_normalizes (inf_le_left.trans hn) hm') hr eJ
  have hlay := semisimple_sqtk c (componentLayer H) componentLayer_idempotent
  have hindex : (normalizer (J' : Set H)).index = 2 :=
    (hJ'.normal_or_index_two_of_layer_odd_rank_le_two hlay.stronglyQuasithin).resolve_left
      (fun hj => hnot (by
        let := hj
        rw [normalizer_eq_top]
        exact le_top))
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
  let N := normalizer (J' : Set H)
  let : N.Normal := normal_of_index_eq_two hindex
  have hdiv : N.relIndex A ∣ 2 := by
    simpa only [show N.index = 2 from hindex] using N.relIndex_dvd_index_of_normal A
  have hirel : N.relIndex A = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun he => hnot (Subgroup.relIndex_eq_one.mp he))
  have horbit : componentOrbit J' A = J' ⊔ J'.map (MulAut.conj a).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two J' A N hirel inf_le_right ha han
  exact not_starred_exchanged_suzuki_support ρ hf hcore J' A hJ' hindex a ha han horbit hA r hr eJ

end CFSG.Quasithin.ChapterD
