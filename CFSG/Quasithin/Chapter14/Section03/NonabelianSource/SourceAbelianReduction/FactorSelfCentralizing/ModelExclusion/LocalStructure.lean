module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion
public import Theory.GroupTheory.QuaternionCentralProductTransport.QuotientExtension
public import Theory.GroupTheory.SpecificGroups.DihedralEightCentralizerProduct

/-!
# The actual quaternion kernel in the marked quotient centralizer

Write C = H ∩ C_G(d), for the original marked point d. The cyclic quotient
map induces a surjection C → C_{C_G(d)/⟨d⟩}(z̄), using the previously proved
nonfusion calculation. Its restriction to U is injective: if d lay in U,
centralization of U would put d in Z(U) ≤ A, contradicting the marking.

The dihedral supplement gives C_{O₂(H)}(d) = U⟨d⟩. Thus the terminal action
of C descends through the cyclic quotient with kernel precisely the embedded
quaternion central product U. Pullback of a subgroup of its action image
constructs the actual normal quaternion subgroup and quotient isomorphism.
The original residual centralizes d, so that image contains O²(Ḣ).

The final conditional assembly reduces the remaining calculation to two
independent obligations: an elementary four-group in the original action image,
and recognition of a subgroup containing such a four-group and the residual
inside S₃ wr C₂. Neither obligation is asserted as proved in this module.
The full quotient-centralizer source theorem remains with this task's assembly.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}
namespace MarkedPoint
variable (P : MarkedPoint F L A)

abbrev localCentralizer : Subgroup G := F.H ⊓ P.globalCentralizer

theorem closure_le_localCentralizer [IsElementaryAbelian 2 V] : F.U ≤ P.localCentralizer := by
  intro u hu
  exact ⟨F.U_le_H hu,mem_centralizer_singleton_iff.mpr (P.mem_supplement.2 u hu)⟩

abbrev localAction : P.localCentralizer →* F.TerminalHdot :=
  (QuotientGroup.mk' F.terminalHatAction.ker).comp (inclusion inf_le_left)

theorem localAction_range : P.localAction.range = F.terminalDot P.localCentralizer := by
  rw [MonoidHom.range_comp]
  change _ = (P.localCentralizer.subgroupOf F.H).map _
  congr 1
  exact inclusion_range inf_le_left

variable (hVA : V ≤ A) (z : G) (hz : F.Vi 1 = zpowers z)

abbrev localQuotientMap : P.localCentralizer →*
    centralizer ({P.pointQuotientMap (P.markedGenerator hVA z hz)} : Set P.PointQuotient) :=
  (P.pointQuotientMap.comp (inclusion inf_le_right)).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    have hc : x.val * z = z * x.val :=
      mem_centralizer_singleton_iff.mp ((F.H_eq_centralizer (by decide) z hz) ▸ x.property.1)
    simp only [MonoidHom.comp_apply]
    rw [←map_mul,←map_mul]
    change P.pointQuotientMap (⟨x.val,x.property.2⟩ * P.markedGenerator hVA z hz) =
      P.pointQuotientMap (P.markedGenerator hVA z hz * ⟨x.val,x.property.2⟩)
    exact congrArg P.pointQuotientMap (Subtype.ext hc))

theorem localQuotientMap_surjective
    (hcomap : (centralizer ({P.pointQuotientMap (P.markedGenerator hVA z hz)} :
      Set P.PointQuotient)).comap P.pointQuotientMap =
      P.localCentralizer.subgroupOf P.globalCentralizer) :
    Function.Surjective (P.localQuotientMap hVA z hz) := by
  intro y
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective P.pointKernel y.val
  have hmem : x ∈ (centralizer ({P.pointQuotientMap (P.markedGenerator hVA z hz)} :
      Set P.PointQuotient)).comap P.pointQuotientMap := by
    change P.pointQuotientMap x ∈ centralizer
      ({P.pointQuotientMap (P.markedGenerator hVA z hz)} : Set P.PointQuotient)
    change P.pointQuotientMap x = y.val at hx
    rw [hx]
    exact y.property
  rw [hcomap] at hmem
  exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

theorem localQuotientMap_ker : (P.localQuotientMap hVA z hz).ker =
    (zpowers P.element).subgroupOf P.localCentralizer := by
  ext x
  rw [MonoidHom.mem_ker,Subtype.ext_iff]
  change P.pointQuotientMap (⟨x.val,x.property.2⟩ : P.globalCentralizer) = 1 ↔
    x.val ∈ zpowers P.element
  rw [←MonoidHom.mem_ker,P.pointQuotientMap_ker,P.pointKernel_eq_subgroupOf]
  rfl

/-- The original quaternion subgroup survives the literal cyclic quotient. -/
theorem closure_quotient_injective (hZ : F.ZU = F.Vi 1) :
    Function.Injective ((P.localQuotientMap hVA z hz).comp
      (F.U.subgroupOf P.localCentralizer).subtype) := by
  have hdU : P.element ∉ F.U := by
    intro hu
    have hc : (⟨P.element,hu⟩ : F.U) ∈ center F.U := by
      apply mem_center_iff.mpr
      intro x
      exact Subtype.ext (P.mem_supplement.2 x x.property)
    have hp : P.element ∈ F.Vi 1 := hZ ▸ mem_map_of_mem F.U.subtype hc
    exact P.outside_factor (hVA (F.le_seed 1 hp))
  have hdis := F.U.disjoint_zpowers_of_prime_order_not_mem P.element
    P.point_order hdU
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hk : (x : P.localCentralizer) ∈ (P.localQuotientMap hVA z hz).ker := hx
  rw [P.localQuotientMap_ker] at hk
  apply Subtype.ext
  apply Subtype.ext
  exact (mem_bot.mp (hdis.eq_bot ▸ (show (x.val:G) ∈ F.U ⊓ zpowers P.element from ⟨x.property,hk⟩)))

/-- A concrete subgroup of the terminal-action image gives the requested
extension in the literal quotient centralizer. -/
theorem quotientCentralizerStructure_of_action_subgroup [IsElementaryAbelian 2 V]
    (hZ : F.ZU = F.Vi 1)
    (dU : QuaternionCentralProductData F.U)
    (hker : F.terminalHatAction.ker = pCore 2 F.H)
    (hcore : F.H.pCoreIn 2 ⊓ P.globalCentralizer = F.U ⊔ zpowers P.element)
    (hcomap : (centralizer ({P.pointQuotientMap (P.markedGenerator hVA z hz)} :
      Set P.PointQuotient)).comap P.pointQuotientMap =
      P.localCentralizer.subgroupOf P.globalCentralizer)
    (S : Subgroup F.TerminalHdot) (hS : S ≤ F.terminalDot P.localCentralizer)
    (hindex : S.relIndex (F.terminalDot P.localCentralizer) ≤ 2)
    (eS : S ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    P.QuotientCentralizerStructure (P.markedGenerator hVA z hz) := by
  have hdC : P.element ∈ P.localCentralizer :=
    ⟨pCoreIn_le 2 F.H P.mem_supplement.1,mem_centralizer_singleton_iff.mpr rfl⟩
  have hk : P.localAction.ker = (F.H.pCoreIn 2).subgroupOf P.localCentralizer := by
    ext x
    change (QuotientGroup.mk' F.terminalHatAction.ker) (⟨x.val,x.property.1⟩ : F.H) = 1 ↔
      x.val ∈ F.H.pCoreIn 2
    rw [←MonoidHom.mem_ker,QuotientGroup.ker_mk',hker]
    exact (mem_map_iff_mem F.H.subtype_injective).symm
  have hkc : (F.H.pCoreIn 2).subgroupOf P.localCentralizer =
      (F.H.pCoreIn 2 ⊓ P.globalCentralizer).subgroupOf P.localCentralizer := by
    ext x
    exact ⟨fun hx => ⟨hx,x.property.2⟩,fun hx => hx.1⟩
  rw [hkc,hcore,subgroupOf_sup P.closure_le_localCentralizer (zpowers_le.mpr hdC),
    ←P.localQuotientMap_ker hVA z hz] at hk
  exact quaternion_extension_of_quotient_action (P.localQuotientMap hVA z hz)
    (P.localQuotientMap_surjective hVA z hz hcomap) P.localAction
    (F.U.subgroupOf P.localCentralizer)
    (dU.map (subgroupOfEquivOfLe P.closure_le_localCentralizer).symm)
    (P.closure_quotient_injective hVA z hz hZ) hk S
    (P.localAction_range.symm ▸ hS) (P.localAction_range.symm ▸ hindex) eS
end MarkedPoint

namespace MarkedPoint
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}

/-- The dihedral calculation identifies the literal action kernel upstairs. -/
theorem local_core_centralizer_eq (P : MarkedPoint F L A)
    [IsElementaryAbelian 2 V] (hVA : V ≤ A) (z : G) (hz : F.Vi 1 = zpowers z)
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1)
    (dU : QuaternionCentralProductData F.U)
    (eD : ↥(F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) ≃* DihedralGroup 4) :
    F.H.pCoreIn 2 ⊓ P.globalCentralizer = F.U ⊔ zpowers P.element := by
  let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzU : z ∈ F.ZU := hZ.symm ▸ hzmem
  have hzD : z ∈ D :=
    ⟨hUQ (map_subtype_le (center F.U) hzU),centerIn_le_centralizer F.U hzU⟩
  have hz2 : orderOf z = 2 := by
    rw [←Nat.card_zpowers,←hz]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hd1 : P.element ≠ 1 := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact A.one_mem
  have hdz : P.element ≠ z := by
    intro he
    apply P.outside_factor
    change P.element ∈ A
    rw [he]
    exact hVA (F.le_seed 1 hzmem)
  have hd2 : P.element^2=1 := by rw [←P.point_order]; exact pow_orderOf_eq_one _
  rw [Recognition.core_eq_U_sup_centralizer F dg hZ dU]
  exact centralizer_inf_of_dihedral_supplement F.U D z P.element inf_le_right eD
    (map_subtype_le (center F.U) hzU) hzD hz1 P.mem_supplement hd2 hd1 hdz
end MarkedPoint

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- All geometric and quotient premises of the extension construction are
proved from the original source hypotheses. Only the indicated subgroup of
the actual terminal-action image remains to be constructed. -/
theorem source_quotientCentralizerStructure_of_action_subgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) (hA : ElementaryFactor F (sourceResidual M Mc) A)
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hgeom : P.FourCenterGeometry z)
    (S : Subgroup F.TerminalHdot) (hS : S ≤ F.terminalDot P.localCentralizer)
    (hindex : S.relIndex (F.terminalDot P.localCentralizer) ≤ 2)
    (eS : S ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz) := by
  let := hA.elementary
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  obtain ⟨eD⟩ := source_factor_supplement_dihedral_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
    hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt
  exact P.quotientCentralizerStructure_of_action_subgroup hA.seed_le z hz hZ dU
    (terminal_kernel_of_center_point F dg hZ)
    (P.local_core_centralizer_eq hA.seed_le z hz dg hZ dU eD)
    (source_quotient_centralizer_comap hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hs A hA P z hz hgeom) S hS hindex eS

/-- The terminal image of the actual marked centralizer contains the full
two-residual, because the original two-residual centralizes the supplement. -/
theorem source_localAction_contains_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) (hA : ElementaryFactor F (sourceResidual M Mc) A)
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A)
    : pResidual 2 F.TerminalHdot ≤ F.terminalDot P.localCentralizer := by
  let := hA.elementary
  have hc := source_factor_residual_centralizes_supplement_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
    hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  rw [←map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
  apply map_mono
  intro x hx
  refine ⟨x.property,?_⟩
  exact mem_centralizer_singleton_iff.mpr
    (hc (mem_map_of_mem F.H.subtype hx) P.element P.mem_supplement).symm

/-- The remaining source placement obligation, expressed in the original
terminal quotient. Its producer supplies a genuine elementary four-subgroup. -/
def TerminalFourSource {T : Sylow 2 G} {V : Subgroup G}
    (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z →
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      ∃ E : Subgroup F.TerminalHdot,
        E ≤ F.terminalDot P.localCentralizer ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4

/-- Conditional assembly of the literal extension. The two inputs concern,
respectively, source placement of a four-group and finite wreath recognition;
neither is asserted here. This task retains their final discharge. -/
theorem quotientCentralizerSource_of_terminal_four_and_wreath_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hfour : TerminalFourSource F (sourceResidual M Mc))
    (hrecognize : ∀ J E : Subgroup BinaryFourPlus.Wreath,
      pResidual 2 BinaryFourPlus.Wreath ≤ J → E ≤ J →
      IsElementaryAbelian 2 E → Nat.card E = 4 →
      ∃ S : Subgroup BinaryFourPlus.Wreath, S ≤ J ∧ S.relIndex J ≤ 2 ∧
        Nonempty (S ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    QuotientCentralizerSource F (sourceResidual M Mc) := by
  intro A hA hlt P z hz hgeom hSylow hcore
  obtain ⟨E,hE,hEA,hEc⟩ := hfour A hA hlt P z hz hgeom hSylow hcore
  let := hEA
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  obtain ⟨eO,_,_⟩ := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let φ : F.TerminalHdot ≃* BinaryFourPlus.Wreath := eO.trans (topEquiv.trans
    (ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
      BinaryFourPlus.isometryEquivWreath))
  let J := F.terminalDot P.localCentralizer
  have hres : pResidual 2 BinaryFourPlus.Wreath ≤ J.map φ.toMonoidHom := by
    rw [←map_pResidual 2 φ]
    exact map_mono (source_localAction_contains_residual
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hA hlt P)
  obtain ⟨S,hS,hindex,⟨eS⟩⟩ := hrecognize (J.map φ.toMonoidHom) (E.map φ.toMonoidHom)
    hres (map_mono hE) (IsElementaryAbelian.map (A:=E) φ.toMonoidHom)
    ((card_map_of_injective φ.injective).trans hEc)
  let S₀ := S.map φ.symm.toMonoidHom
  have hback : (J.map φ.toMonoidHom).map φ.symm.toMonoidHom = J := by
    rw [map_map]
    have heq : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact φ.symm_apply_apply x
    rw [heq,Subgroup.map_id]
  have hS₀ : S₀ ≤ J := hback ▸ map_mono (f:=φ.symm.toMonoidHom) hS
  have hi₀ : S₀.relIndex J ≤ 2 := by
    have hh := relIndex_map_map_of_injective (f:=φ.symm.toMonoidHom) S (J.map φ.toMonoidHom) φ.symm.injective
    rw [hback] at hh
    exact hh.symm ▸ hindex
  exact source_quotientCentralizerStructure_of_action_subgroup
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hA hlt P z hz hgeom
    S₀ hS₀ hi₀ ((φ.symm.subgroupMap S).symm.trans eS)
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
