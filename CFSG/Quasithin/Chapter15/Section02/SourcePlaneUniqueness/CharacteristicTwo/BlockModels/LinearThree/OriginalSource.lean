module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.CoreTransport
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Setup

/-!
# The original binary C.2.7 MS description in the preliminary reduction

The radical is R = O₂(M ∩ I), not QI = O₂(KS). The original plane lies
in R and in the omega-center of S ∩ XR; that intersection is Sylow because
R normalizes the original component. Escape of the component excludes the
central-omega clause of C.1.34(5). The four remaining alternatives are retained
with their literal section models, transported to the common intrinsic
commutator core of XR and XQI. Radical inequalities still refer to XR.

This is the actual C.2.7(g) consumer of CoreTransport. Cases (2)--(4) are eliminated
in NonblockExclusion by the separate MS construction on XQI.
The earlier Kc orbit premise retains the plane-geometry and small-parabolic
producers and final discharge by the plane-uniqueness assembly.
Source: Aschbacher--Smith C.1.34, C.2.7(g), preliminary 15.2.23,
printed pp.136--137,145,1115--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Characteristic two places the original plane in the literal C.2.7 radical. -/
theorem plane_le_intersection_radical
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I) :
    ZS ≤ (M ⊓ I).pCoreIn 2 := by
  have hSM : planeSylow T ZS ≤ M := inf_le_left.trans hsource.maximal.1.2
  have hQN : I.pCoreIn 2 ≤ M ⊓ I :=
    le_inf ((d.core_le_plane hI).trans hSM) (pCoreIn_le 2 I)
  have hcore : I.pCoreIn 2 ≤ (M ⊓ I).pCoreIn 2 := by
    have hh := inf_pCoreIn_le_of_le 2 (show M ⊓ I ≤ I from inf_le_right)
    simpa only [inf_eq_right.mpr hQN] using hh
  exact (show ZS ≤ I.pCoreIn 2 from fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ z).mp
      (d.plane_le_escape_core_omega hI hfit hz)).1).trans hcore

/-- The C.2.7 radical is contained in the original Sylow subgroup S. -/
theorem intersection_radical_le_plane (hI : PlaneEscapes Mc ZS I) :
    (M ⊓ I).pCoreIn 2 ≤ planeSylow T ZS := by
  have hSN : planeSylow T ZS ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 (planeSylow T ZS) I from
    d.sylow_in_escape hI).restrict hSN inf_le_right
  exact (pCoreIn_le_sylow (M ⊓ I) P).trans_eq hP

/-- The original Sylow intersection remains Sylow after adjoining a normalizing radical. -/
theorem component_radical_extension_sylow
    (hI : PlaneEscapes Mc ZS I) {X R : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I)
    (hRS : R ≤ planeSylow T ZS) (hRX : R ≤ normalizer (X : Set G)) :
    Chapter1.IsSylowIn 2 (planeSylow T ZS ⊓ (X ⊔ R)) (X ⊔ R) := by
  have hRI : R ≤ I := hRS.trans
    ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  obtain ⟨S,hS⟩ := d.sylow_in_escape hI
  have hRS' : R.subgroupOf I ≤ (S : Subgroup I) := by
    intro r hr
    have hh := hRS hr
    rw [←hS] at hh
    obtain ⟨a,ha,he⟩ := hh
    exact (Subtype.ext he : a = r) ▸ ha
  have hn : R.subgroupOf I ≤ normalizer (X.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hX.1]
    exact fun _ hr => hRX hr
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_sup_of_normalized (X.subgroupOf I)
    (R.subgroupOf I) hRS' hn (S.exists_subgroupOf_eq_of_subnormal _ hX.2.subnormal)
  have hs : Chapter1.IsSylowIn 2
      ((S : Subgroup I) ⊓ (X.subgroupOf I ⊔ R.subgroupOf I))
      (X.subgroupOf I ⊔ R.subgroupOf I) :=
    ⟨P,by rw [hP,subgroupOf_map_subtype]⟩
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs I.subtype
  rwa [Subgroup.map_inf _ _ _ I.subtype_injective,hS,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hX.1,map_subgroupOf_eq_of_le hRI] at hm

/-- The original plane lies in the local Sylow omega-center for XR. -/
theorem intersection_radical_omega_contains
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (X : Subgroup G) :
    ZS ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (planeSylow T ZS ⊓ (X ⊔ (M ⊓ I).pCoreIn 2)) := by
  intro z hz
  have hzs := (mem_omegaOneCenterAmbient_iff _ _).mp (d.omega_center ▸ hz)
  change z ∈ omegaOneCenterAmbient _
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨⟨hzs.1,mem_sup_right (d.plane_le_intersection_radical hI hfit hz)⟩,
      hzs.2.1,fun s hs => hzs.2.2 s hs.1⟩

/-- The genuine MS hypotheses force escape for the original binary component. -/
theorem LinearThree.Branch.binary_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F) : ¬ X ≤ Mc := by
  let A := X.subgroupOf I
  let a : A ≃* X := subgroupOfEquivOfLe b.input.component.1
  have hA : A.map I.subtype = X := map_subgroupOf_eq_of_le b.input.component.1
  obtain ⟨e⟩ := b.ms.1.model
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [←Nat.card_eq_fintype_card,pow_one] using b.field_card)).symm
  let eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL :=
    (((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e).trans
      (Atlas.fieldEquivSL 3 f)).trans Matrix.PSL3Two.equiv
  have hh := d.linearThree_ms_component_not_le_partner horbit hI
    b.input.component.2 eA (isPGroup_pCoreIn 2 (M ⊓ I))
      (hA.symm ▸ b.ms.1)
  simpa only [map_subgroupOf_eq_of_le b.input.component.1] using hh

/-- The central-omega clause of case (5) is impossible on the original radical. -/
theorem LinearThree.Branch.binary_omega_not_central
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F) :
    ¬ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (planeSylow T ZS ⊓ (X ⊔ (M ⊓ I).pCoreIn 2)) ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (X ⊔ (M ⊓ I).pCoreIn 2) := by
  intro hc
  apply b.binary_not_le_partner d horbit hI
  apply le_trans ?_ ((d.centralizer_le_intersection hI).trans inf_le_left)
  intro x hx z hz
  obtain ⟨a,ha,he⟩ := hc (d.intersection_radical_omega_contains hI hfit X hz)
  have hh := congrArg Subtype.val
    (mem_center_iff.mp ha (⟨x,mem_sup_left hx⟩ : (X ⊔ (M ⊓ I).pCoreIn 2 : Subgroup G)))
  change x * (a : G) = (a : G) * x at hh
  change (a : G) = z at he
  rw [he] at hh
  exact hh.symm

omit d in
/-- The three non-block rows, with their module sections written on Q.
The radical inequality and relative centrality still concern the original XR. -/
@[expose] def LinearThree.NonblockCoreRows (X R S Q : Subgroup G) (n : ℕ) (F : Type)
    [Field F] (e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F) : Prop :=
  let Z := Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
  let C := Q ⊓ centralizer (X : Set G)
  let U := ⁅Z,X⁆
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let a := linearThreeActor e
  let v := Representation.specialLinearNatural (k := F) 3
  (HasSectionModel X Q ⊥ a (v.prod v) ∧ MSNotCentralizerCore X R S) ∨
  (HasSectionModel X Z ⊥ a v ∧ HasSectionModel X Q Z a (v.dual.prod v.dual) ∧
    MSNotCentralizerCore X R S) ∨
  (IsElementaryAbelian 2 C ∧ Nat.card C = 2 ^ (2 * n) ∧
    C ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (X ⊔ R) ∧ Z = C ⊔ U ∧ C ⊓ U = ⊥ ∧
    HasSectionModel X U ⊥ a v ∧ HasSectionModel X Phi Z a v.dual ∧
    HasSectionModel X D Phi a (v.dual.prod v.dual) ∧
    HasSectionModel X Q D a (v.prod v) ∧ MSNotCentralizerCore X R S)

/-- Apply the original C.2.7(g) description at its actual Sylow intersection.
Case (5) is impossible; all module sections in the other rows use the same
intrinsic core as XQI. The original radical inequalities are retained. -/
theorem LinearThree.Branch.binary_preliminary_core_cases
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F) :
    (ChapterC.IsBlock (X.subgroupOf I) ∧ ChapterC.IsSL3EvenBlock X 1 ∧
      ∃ e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        HasSectionModel X (msQ X (planeParabolicCore T H ZS)) ⊥
          (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3)) ∨
    ∃ e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      LinearThree.NonblockCoreRows X ((M ⊓ I).pCoreIn 2)
        (planeSylow T ZS ⊓ (X ⊔ (M ⊓ I).pCoreIn 2))
        (msQ X (planeParabolicCore T H ZS)) 1 F e := by
  have hs := d.component_radical_extension_sylow hI b.input.component
    (d.intersection_radical_le_plane hI) b.input.normalizes
  have hr := le_inf (d.intersection_radical_le_plane hI)
    (show (M ⊓ I).pCoreIn 2 ≤ X ⊔ (M ⊓ I).pCoreIn 2 from le_sup_right)
  obtain ⟨e,hcases⟩ := b.ms.2 _ hs hr
  have he := d.plane_component_msCore_eq hI b.input.component b.ms.1
  rcases hcases with h | h | h | h | h
  · refine Or.inl ⟨⟨inferInstance,?_,b.input.component.2.subnormal⟩,h.2.1,e,?_⟩
    · exact h.2.1.2.1.of_mulEquiv (subgroupOfEquivOfLe b.input.component.1).symm
    · rw [←he]
      exact h.2.2
  · refine Or.inr ⟨e,?_⟩
    rw [←he]
    exact Or.inl h
  · refine Or.inr ⟨e,?_⟩
    rw [←he]
    exact Or.inr (Or.inl h)
  · refine Or.inr ⟨e,?_⟩
    rw [←he]
    exact Or.inr (Or.inr h)
  · exact (b.binary_omega_not_central d horbit hI hfit h.2.2.2.1).elim

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
