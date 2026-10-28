module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianSeed
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.ThreeSubgroups

/-!
# The natural center constituent in the remaining branch of 12.9.4

The original point component has PSL₄(2) quotient. The proved A.3.12
comparison gives equality, PSL₅(2), M₂₄ or J₄ for every containing local
component, retaining the intrinsic two-core quotients. The preferred
choice excludes PSL₅(2). The seven actual module alternatives of 12.2.2
exclude M₂₄ and J₄, so the point component is maximal faithful and
NaturalReduction applies to each of its chosen constituents.

The module theorem is an explicit earlier-source input; Structural1222
alone does not contain it. Its guarded version suffices: the escaping
point normalizer constructs two distinct maximal two-local overgroups
of the original Sylow subgroup.

The constituent inside Z(U) has order sixteen and its returning-center
fixed subgroup has order four. The center supplement and the relative
three-subgroups lemma identify this same constituent with [Z(U),K₁],
so the original point normalizer preserves it. The final consumer
constructs all these data from the unchanged flag and quotient action.
The later parabolic contradiction and discharge of the earlier module
input remain with the natural-branch assembly.

Source: Aschbacher--Smith 12.9.2 and 12.9.4, printed pp.857,859--860
of refs/quasithin.pdf, using A.3.12 and 12.2.2(3).
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem local_join_sqtk
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) :
    IsSQTK KnownSimple.IsKnownSimple (J ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := J ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R,hJ.2.2,isPGroup_pCoreIn 2 H,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

/-- The literal containing local member has exactly the restricted A.3.12 alternatives. -/
theorem nonabelian_caseFive_containing_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : C.K1 ≤ J) :
    C.K1 = J ∨ LargePointModel (J ⧸ pCore 2 J) := by
  let H := J ⊔ (T : Subgroup G)
  have ht : (T : Subgroup G) ≤ H := le_sup_right
  have hk : C.K1 ≤ H := hKJ.trans le_sup_left
  have hl : C.K1.subgroupOf H ∈ Chapter1.L H (T.subtype ht) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf ht hk).mp
        ⟨hk,nonabelian_point_component_local h F C⟩
  have hn : (T.subtype ht : Subgroup H) ≤ normalizer (C.K1.subgroupOf H : Set H) := by
    intro t ht b
    exact ((F.invariant 1).trans
      ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)) ht (b : G)
  let eK := subgroupOfEquivOfLe hk
  have hm := (nonabelian_caseFive_point_core_model h earlier F hne B h5 C).of_mulEquiv
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  have ha := ChapterA.Section03.SourceEmbeddings.AlternatingEight.restricted_containing_models
    (local_join_sqtk h.source.simpleQTKE hJ) (T.subtype ht) hl.1 hJ.1
    (comap_mono hKJ) hn hm
  let eJ := subgroupOfEquivOfLe (show J ≤ H from le_sup_left)
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  rcases ha with he | hm | hm | hm
  · exact .inl ((map_subgroupOf_eq_of_le hk).symm.trans
      ((congrArg (map H.subtype) he).trans (map_subgroupOf_eq_of_le le_sup_left)))
  · exact .inr (.inl (hm.of_mulEquiv eQ.symm))
  · exact .inr (.inr (.inl ⟨eQ.symm.trans hm.some⟩))
  · exact .inr (.inr (.inr ⟨eQ.symm.trans hm.some⟩))

/-- The containing component's original two-core quotient is quasisimple. -/
theorem nonabelian_caseFive_containing_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : C.K1 ≤ J) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  let H := J ⊔ (T : Subgroup G)
  let K := C.K1.subgroupOf H
  let A := J.subgroupOf H
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  have ht : (T : Subgroup G) ≤ H := le_sup_right
  have hk : C.K1 ≤ H := hKJ.trans le_sup_left
  have hl : K ∈ Chapter1.L H (T.subtype ht) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf ht hk).mp
        ⟨hk,nonabelian_point_component_local h F C⟩
  have hn : (T.subtype ht : Subgroup H) ≤ normalizer (K : Set H) := by
    intro t ht b
    exact ((F.invariant 1).trans
      ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)) ht (b : G)
  let eK := subgroupOfEquivOfLe hk
  have hm := (nonabelian_caseFive_point_core_model h earlier F hne B h5 C).of_mulEquiv
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (local_join_sqtk h.source.simpleQTKE hJ) N pCore_isPGroup
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']; infer_instance
  obtain ⟨hl',_,hm'⟩ := ChapterA.Section03.SourceEmbeddings.AlternatingEight.local_section_map
    hl.1 hn hm q
  let S := (T.subtype ht).mapSurjective (QuotientGroup.mk'_surjective N)
  let : IsQuasisimple (A.map q) :=
    ChapterA.Section03.SourceEmbeddings.AlternatingEight.containing_quasisimple
      hQ (pCore_quotient_pCore_eq_bot 2) S hl' (hJ.1.map_quotient N)
      (map_mono (comap_mono hKJ)) hm'
  let eJ := subgroupOfEquivOfLe (show J ≤ H from le_sup_left)
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  exact IsQuasisimple.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hJ.1).symm.trans eQ)

/-- Every simple actor in the genuine seven-module theorem has order prime to 23. -/
theorem chosen_simple_core_not_twentyThree
    {J I : Subgroup G} (c : ChosenModule T J I)
    (hs : IsSimpleGroup (J ⧸ pCore 2 J)) (rows : ModuleAlternatives1222 c) :
    ¬ 23 ∣ Nat.card (J ⧸ pCore 2 J) := by
  have hlinear (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (e : (J ⧸ pCore 2 J) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      ¬ 23 ∣ Nat.card (J ⧸ pCore 2 J) := by
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl | rfl
    · rw [Atlas.Comparisons.Exceptional.sl3Two_card]; decide
    · rw [Atlas.Order20160A8.sl4Two_card]; decide
    · rw [Representation.SL5ExteriorSquare.card_specialLinearFive]; decide
  let := c.actionCentralizer_normal
  have halt (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (e : (J ⧸ (centralizer (I : Set G)).subgroupOf J) ≃* alternatingGroup (Fin n)) :
      ¬ 23 ∣ Nat.card (J ⧸ pCore 2 J) := by
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr ((c.coreToFaithfulEquiv hs).trans e).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  cases rows with
  | linear n hn a => exact hlinear n hn a.groupEquiv
  | linearThreeExtension e _ _ => exact hlinear 3 (.inl rfl) e
  | linearFiveExterior e _ _ => exact hlinear 5 (.inr (.inr rfl)) e
  | alternating n hlo hhi a => exact halt n hlo hhi a.groupEquiv
  | alternatingSevenFour e _ => exact halt 7 (by decide) (by decide) e
  | g2 a =>
    rw [Nat.card_congr a.groupEquiv.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
  | tripleSix e _ _ _ =>
    rw [Nat.card_congr e.toEquiv,Atlas.Codes.hexEven_card]
    decide

/-- The sporadic strict overgroups are excluded by the original module rows,
not by the structural prefix of 12.2.2. -/
theorem chosen_core_not_large_sporadic
    {J I : Subgroup G} (c : ChosenModule T J I)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (rows : ModuleAlternatives1222 c) :
    ¬ (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  intro hspor
  rcases hspor with hspor | hspor
  · obtain ⟨e⟩ := hspor
    let := Sporadic.Mathieu.m24_isSimpleGroup
    have hh := chosen_simple_core_not_twentyThree c e.isSimpleGroup rows
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order] at hh
    exact hh (by decide)
  · obtain ⟨e⟩ := hspor
    let := hq
    let : IsQuasisimple Janko4.Model := IsQuasisimple.of_mulEquiv e
    let : IsSimpleGroup (Janko4.Model ⧸ center Janko4.Model) := IsQuasisimple.simple
    let a := (QuotientGroup.quotientMulEquivOfEq Janko4.model_center_eq_bot).trans
      QuotientGroup.quotientBot
    let : IsSimpleGroup Janko4.Model := a.symm.isSimpleGroup
    have hh := chosen_simple_core_not_twentyThree c e.isSimpleGroup rows
    rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hh
    exact hh (by decide)

/-- The actual escaping point normalizer supplies the multiple-overgroup
guard needed by the independent module source. -/
theorem natural_flag_many_maximalTwoLocals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  obtain ⟨N,hHN,hN⟩ := Finite.exists_le_maximal (Gi_twoLocal h F 1 le_rfl)
  apply Set.one_lt_ncard_iff_nontrivial.mpr
  refine ⟨normalizer (L : Set G),
    ⟨(h.maximal_unique earlier.structural earlier.uniqueness).1,
      h.sylow_normalizes earlier.structural⟩,
    N,⟨hN,(F.invariant 1).trans hHN⟩,?_⟩
  intro he
  exact h.flag_escape F earlier.alternatives (hHN.trans_eq he.symm)

/-- The source hypothesis for each faithful maximal overgroup, with the
original global exclusions inherited from the original higher-rank input. -/
theorem nonabelian_caseFive_maximal_hypothesis
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {J : Subgroup G}
    (hJ : FaithfulMaximalLocal T J) (hKJ : C.K1 ≤ J) :
    Hypothesis1223 KnownSimple.IsKnownSimple T J :=
  { simpleQTKE := h.source.simpleQTKE
    maximal_faithful := hJ
    quasisimple := nonabelian_caseFive_containing_quasisimple h earlier F hne B h5 C hJ.1.1 hKJ
    no_rankTwo := h.source.no_rankTwo
    no_M22 := h.source.no_M22
    no_M23 := h.source.no_M23
    no_J4 := h.source.no_J4 }

/-- Without the module part of 12.2.2, the exact remaining obstruction to
maximality is an actual faithful maximal M₂₄ or J₄ overgroup. -/
theorem nonabelian_caseFive_maximal_or_sporadic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    FaithfulMaximalLocal T C.K1 ∨
      ∃ J : Subgroup G, C.K1 < J ∧ Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
        (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∨
          Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  obtain ⟨J,hKJ,hJ⟩ := nonabelian_point_exists_faithful_maximal h earlier F hne g hgP hgH B h5 C
  have hj := nonabelian_caseFive_maximal_hypothesis h earlier F hne B h5 C hJ hKJ
  by_cases he : C.K1 = J
  · exact .inl (he.symm ▸ hJ)
  · right
    refine ⟨J,lt_of_le_of_ne hKJ he,hj,?_⟩
    rcases nonabelian_caseFive_containing_models h earlier F hne B h5 C hJ.1.1 hKJ with he' | hm | hm
    · exact (he he').elim
    · exact (preferred rfl J hj hm).elim
    · exact hm

/-- Source 12.9.2 and A.3.12 make the actual point component maximal.
The genuine same-ambient module theorem is explicit, separately from the
structural prefix in EarlierSetupResults. -/
theorem nonabelian_caseFive_maximal_of_modules
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) : FaithfulMaximalLocal T C.K1 := by
  rcases nonabelian_caseFive_maximal_or_sporadic h preferred earlier F hne g hgP hgH B h5 C
      with hm | ⟨J,_,hj,hspor⟩
  · exact hm
  · obtain ⟨⟨I,⟨c⟩⟩⟩ := (earlier.structural G T J hj).2.1
    exact (chosen_core_not_large_sporadic c hj.quasisimple (modules J I hj c) hspor).elim

/-- NaturalReduction now applies to every actual chosen constituent of K₁,
with the literal quotient, original module and conjugation marking retained. -/
theorem nonabelian_caseFive_chosen_natural_of_modules
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I) :
    NaturalModule c 4 := by
  have hm := nonabelian_caseFive_maximal_of_modules modules h preferred earlier F hne g hgP hgH B h5 C
  exact four G T C.K1 I
    (nonabelian_caseFive_maximal_hypothesis h earlier F hne B h5 C hm le_rfl) c
    (nonabelian_caseFive_point_core_model h earlier F hne B h5 C)

/-- The original constituent is exactly the commutator of Z(U) with K₁.
The proof uses the returning-center supplement and the relative
three-subgroups lemma, with no normality in the ambient simple group. -/
theorem nonabelian_caseFive_chosen_eq_center_commutator
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) : I = ⁅F.ZU,C.K1⁆ := by
  have hm := nonabelian_caseFive_maximal_of_modules modules h preferred earlier F hne g hgP hgH B h5 C
  have hj := nonabelian_caseFive_maximal_hypothesis h earlier F hne B h5 C hm le_rfl
  have hTI := ((earlier.structural G T C.K1 hj).2.2 I c).1
  obtain ⟨_,_,_,_,_,_,_,_,hXT,_⟩ := nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let D := conjugate F.ZU g
  let A := F.ZU ⊓ centralizer (D : Set G)
  have hDI : D ≤ normalizer (I : Set G) := (F.conjugate_ZU_le_X g).trans (hXT.trans hTI)
  have hZI : F.ZU ≤ normalizer (I : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hiZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hKZ : C.K1 ≤ normalizer (F.ZU : Set G) := C.point_le.trans
    ((le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_characteristic_image F.U (center F.U)))
  have hZD : ⁅F.ZU,D⁆ ≤ I := by
    rw [←nonabelian_caseFive_chosen_covers_center h earlier F hne g hgP hgH B h5 C c hiZ]
    apply commutator_sup_le_of_relative_normal F.ZU A I D I hZI inf_le_left hiZ
    · exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
    · exact le_normalizer_iff_commutator_le_left.mp hDI
  have hKZI : ⁅C.K1,F.ZU⁆ ≤ I := by
    rw [←nonabelian_caseFive_component_commutator h earlier F hne g hgP hgH B h5 C]
    apply commutator_commutator_le_of_rotate_of_le_normalizer c.normalizes hDI hZI
    · exact (commutator_mono (show ⁅D,F.ZU⁆ ≤ I by rwa [commutator_comm]) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp c.normalizes)
    · exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hKZ) le_rfl).trans hZD
  apply le_antisymm
  · rw [c.eq_commutator]
    exact commutator_mono hiZ le_rfl
  · rwa [commutator_comm]

/-- The original point normalizer, hence its plane intersection, preserves
the actual chosen constituent. -/
theorem nonabelian_caseFive_point_normalizes_chosen
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) : F.H ≤ normalizer (I : Set G) := by
  rw [nonabelian_caseFive_chosen_eq_center_commutator modules h preferred earlier F hne g hgP hgH B h5 C c hiZ]
  have hnZ : F.H ≤ normalizer (F.ZU : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_characteristic_image F.U (center F.U))
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hnZ ha)]
  rw [mem_normalizer_iff_map_conj_eq.mp
    (((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal) ha)]

/-- The source's actual constituent is natural of order sixteen, covers the
center quotient, and has returning-center fixed subgroup of order four. -/
theorem nonabelian_caseFive_natural_constituent_of_modules
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (C : ComponentGeometry F L) (I : Subgroup G) (c : ChosenModule T C.K1 I),
      NaturalModule c 4 ∧ I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧
      (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU ∧
      I = ⁅F.ZU,C.K1⁆ ∧ F.H ≤ normalizer (I : Set G) ∧
      Nat.card I = 16 ∧ Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4 := by
  obtain ⟨C⟩ := componentGeometry earlier h (.inl rfl) F
  obtain ⟨I,⟨c⟩,hi,hz,he,hidx⟩ :=
    nonabelian_center_exists_rank_two_chosen h earlier F hne g hgP hgH B h5 C
  have hn := nonabelian_caseFive_chosen_natural_of_modules modules h preferred earlier four
    F hne g hgP hgH B h5 C c
  let := c.elementary
  obtain ⟨m⟩ := hn
  have hc : Nat.card I = 16 := by
    calc
      Nat.card I = Nat.card (Additive I) := rfl
      _ = Nat.card (Fin 4 → ZMod 2) := Nat.card_congr m.coordinates.toEquiv
      _ = 16 := by rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide
  refine ⟨C,I,c,⟨m⟩,hi,hz,he,
    nonabelian_caseFive_chosen_eq_center_commutator modules h preferred earlier F hne g hgP hgH B h5 C c hz,
    nonabelian_caseFive_point_normalizes_chosen modules h preferred earlier F hne g hgP hgH B h5 C c hz,hc,?_⟩
  let A := I ⊓ centralizer (conjugate F.ZU g : Set G)
  have hm := (A.subgroupOf I).card_mul_index
  have ha : Nat.card (A.subgroupOf I) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe (show A ≤ I from inf_le_left)).toEquiv
  change Nat.card (A.subgroupOf I) * A.relIndex I = Nat.card I at hm
  rw [ha,hidx,hc] at hm
  change Nat.card A = 4
  omega

/-- Literal application of the guarded module producer: the guard is
constructed from the original flag, and the seed constituent retains its
actual natural action, center quotient and returning-center centralizer. -/
theorem nonabelian_caseFive_natural_constituent_of_module_source
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (C : ComponentGeometry F L) (I : Subgroup G) (c : ChosenModule T C.K1 I),
      NaturalModule c 4 ∧ I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧
      (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU ∧
      I = ⁅F.ZU,C.K1⁆ ∧ F.H ≤ normalizer (I : Set G) ∧
      Nat.card I = 16 ∧ Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4 :=
  nonabelian_caseFive_natural_constituent_of_modules
    (modules.at T (natural_flag_many_maximalTwoLocals h earlier F))
    h preferred earlier four F hne g hgP hgH B h5

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
