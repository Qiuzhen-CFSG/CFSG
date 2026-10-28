module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCenterQuotient
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Theory.GroupTheory.ConjugateSpanSupplement
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness
public import Theory.GroupTheory.SylowFixedSpanReduced
public import Theory.SpecificGroups.AlternatingEight.ReducedCover

/-!
# The original center seed and its chosen constituents in 12.9.4

The literal parabolics generate LT. If the point component centralized
Z_D = Ω₁(Z(T)) intersect Z(I₂), uniqueness of the maximal two-local would
force the point residual to be normal, contradicting nonabelianity of U.
The orbit V_D of this seed lies in Z(U); Sylow inheritance makes it reduced
in K₁T. Its nonzero commutator gives faithful local membership and a chosen
Irr⁺ constituent inside the same orbit.

The returning center D = Z(U)^g satisfies [K₁,D] = K₁. Thus every chosen
constituent is moved by D. The proved L₀-irreducibility on the original
center quotient makes each constituent in Z(U) cover that quotient, so
its literal D-centralizer has index four. The final consumer constructs
this data for the original component, without any new source premise.

The original action also identifies K₁/O₂(K₁) with the dotted actor.
The nonquasisimple seven-core alternative cannot surject onto A₈, and
Schur's reduced-cover theorem removes the kernel in the quasisimple case.
The resulting equivalence retains its commuting identity with the original
quotient projection and supplies the PSL₄(2) premise of NaturalReduction.
Maximality, the natural-module identification, and the ensuing parabolic
contradiction remain with the natural-branch assembly owner.

Source: Aschbacher--Smith 12.8.13(5) and 12.9.4, printed pp.855--856
and859--860 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original first parabolic and point-residual/Sylow join generate LT. -/
theorem four_point_parabolic_generate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) :
    F.P L ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G) := by
  let := h.chosen.elementary
  apply le_antisymm
  · exact sup_le inf_le_left (sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl)
  · rw [← F.orderedParabolic_generation_of_full_binary_action (by decide) L
      h.chosen.normalizes h.full_L_action]
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    by_cases he : j = 1
    · subst j
      rw [F.orderedParabolic_one]
      exact le_sup_left
    · have hPH : F.orderedParabolic L j ≤ F.H :=
        F.orderedParabolic_le_H (by decide) L (by omega)
      exact (le_inf inf_le_left hPH).trans
        ((point_residual_sylow_eq_intersection h earlier F).ge.trans le_sup_right)

/-- Removing the first parabolic two-core gives the literal source generation by I₂ and L₁T. -/
theorem four_I2_point_sylow_generate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.I₂ L ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G) := by
  let := h.chosen.elementary
  obtain ⟨hc,hs⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hspan := F.U_eq_plane_span L (by decide) h.chosen.normalizes
    (F.localKernel_irreducible L (by decide) h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  have hf := (F.binary_two_conjugate_generation (by decide) L h.chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
    hs hspan hne g hgP hgH).2
  have hTP : (T : Subgroup G) ≤ F.P L :=
    (F.sylow_le_orderedParabolic L 1).trans (F.orderedParabolic_one L).le
  have hcore : (F.P L).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP] using
      pCoreIn_le_sylow (F.P L) (T.subtype hTP)
  rw [←four_point_parabolic_generate h earlier F]
  apply le_antisymm
  · exact sup_le_sup (le_sup_right.trans hf.ge) le_rfl
  · apply sup_le _ le_sup_right
    rw [hf]
    exact sup_le (hcore.trans (le_sup_right.trans le_sup_right)) le_sup_left

/-- The source seed Z_D in the original ambient group. -/
@[expose] def nonabelianCenterSeed (F : InvariantFlag T V 4) (L : Subgroup G) : Subgroup G :=
  sylowOmega T ⊓ Section08.centerIn (F.I₂ L)

/-- The orbit of the source center seed under the specified point component. -/
@[expose] def nonabelianCenterModule (F : InvariantFlag T V 4) (L K : Subgroup G) : Subgroup G :=
  conjugateSpanBy (nonabelianCenterSeed F L) K

/-- The original point component moves the source seed; uniqueness of the maximal two-local excludes centralization. -/
theorem nonabelian_center_seed_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) : ⁅nonabelianCenterSeed F L,C.K1⁆ ≠ ⊥ := by
  intro he
  let Z := nonabelianCenterSeed F L
  have hKC : C.K1 ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (inf_le_left.trans (sylowOmega_centralizes T))
  have hIC : F.I₂ L ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centerIn_le_centralizer _))
  have hLTC : L ⊔ (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    rw [←four_I2_point_sylow_generate h earlier F hne g hgP hgH]
    exact sup_le hIC (sup_le (C.contains.trans hKC) hTC)
  have hneZ : Z ≠ ⊥ :=
    nonabelian_caseFive_omega_center_intersection h (Or.inl rfl) earlier F hne g hgP hgH B h5
  let := sylowOmega_elementary T
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le (show Z ≤ sylowOmega T from inf_le_left)
  have hNZ : normalizer (Z : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    · exact IsElementaryAbelian.isPGroup 2 Z
    · exact hneZ
    · exact hLTC.trans (Subgroup.centralizer_le_normalizer _)
  have heK := component_eq_of_le_normalizer h earlier F 1 (Or.inr ⟨rfl,Or.inl rfl⟩)
    ⟨C.point_le,C.component⟩ C.contains
    ((hKC.trans (Subgroup.centralizer_le_normalizer _)).trans hNZ)
  exact hne (point_span_abelian_of_point_residual_normal h (Or.inl rfl) earlier F
    (heK ▸ C.normal))


/-- The orbit of the center seed stays in the actual center Z(U). -/
theorem nonabelian_center_module_le_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (C : ComponentGeometry F L) : nonabelianCenterModule F L C.K1 ≤ F.ZU := by
  have hm := (nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1
  apply conjugateSpanBy_le
  · exact inf_le_right.trans (hm.ge.trans inf_le_left)
  · exact C.point_le.trans ((le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_characteristic_image F.U (center F.U)))

/-- Sylow inheritance makes the literal seed orbit reduced inside K₁T. -/
theorem nonabelian_center_module_reduced
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (C : ComponentGeometry F L) :
    IsPReduced 2 ((nonabelianCenterModule F L C.K1).subgroupOf (C.K1 ⊔ (T : Subgroup G))) := by
  let Z := nonabelianCenterSeed F L
  let J := C.K1 ⊔ (T : Subgroup G)
  have hZJ : Z ≤ J := (inf_le_left.trans (sylowOmega_le T)).trans le_sup_right
  have hZT : Z ≤ centralizer (T : Set G) := inf_le_left.trans (sylowOmega_centralizes T)
  have hTK : (T : Subgroup G) ≤ normalizer (C.K1 : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hspan : conjugateSpanBy Z J = nonabelianCenterModule F L C.K1 :=
    conjugateSpanBy_sup_of_normalizes_seed Z C.K1 (T : Subgroup G)
      ((le_centralizer_iff.mp hZT).trans (Subgroup.centralizer_le_normalizer _)) hTK
  let := sylowOmega_elementary T
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le (show Z ≤ sylowOmega T from inf_le_left)
  let : IsElementaryAbelian 2 (Z.subgroupOf J) := IsElementaryAbelian.subgroupOf hZJ
  have hn : normalClosure (Z.subgroupOf J : Set J) =
      (nonabelianCenterModule F L C.K1).subgroupOf J :=
    (normalClosure_subgroupOf_eq_conjugateSpanBy Z J hZJ).trans (congrArg (subgroupOf · J) hspan)
  have hc : IsMulCommutative (normalClosure (Z.subgroupOf J : Set J)) := by
    rw [hn]
    have hh := nonabelian_center_module_le_center h earlier F hne g hgP hgH C
    let : IsMulCommutative (nonabelianCenterModule F L C.K1) :=
      le_centralizer_iff_isMulCommutative.mp
        (hh.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (centralizer_le hh)))
    infer_instance
  let := hc
  have hz : Z.subgroupOf J ≤ centralizer (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right) : Set J) := by
    intro z hz t ht
    exact Subtype.ext (hZT hz t ht)
  rw [←hn]
  exact isPReduced_normalClosure_of_sylow_central (T.subtype le_sup_right)
    (Z.subgroupOf J) (comap_mono (inf_le_left.trans (sylowOmega_le T))) hz

/-- The constructed point component belongs to the original local family L(G,T). -/
theorem nonabelian_point_component_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L) :
    C.K1 ∈ Chapter1.L G (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  exact Chapter1.mem_L_of_cComponent (H := F.H)
    (Chapter1.mem_H_of_isTwoLocal (Gi_twoLocal h F 1 le_rfl))
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
    C.point_le C.component


/-- The nonzero seed action survives in the intrinsic commutator inside K₁T. -/
theorem nonabelian_center_module_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ⁅(nonabelianCenterModule F L C.K1).subgroupOf (C.K1 ⊔ (T : Subgroup G)),
      C.K1.subgroupOf (C.K1 ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  intro he
  apply nonabelian_center_seed_moved h earlier F hne g hgP hgH B h5 C
  have hZJ : nonabelianCenterSeed F L ≤ C.K1 ⊔ (T : Subgroup G) :=
    (inf_le_left.trans (sylowOmega_le T)).trans le_sup_right
  have hMJ : nonabelianCenterModule F L C.K1 ≤ C.K1 ⊔ (T : Subgroup G) :=
    conjugateSpanBy_le hZJ (le_sup_left.trans (C.K1 ⊔ (T : Subgroup G)).le_normalizer)
  have hm := congrArg (map (C.K1 ⊔ (T : Subgroup G)).subtype) he
  rw [map_commutator,map_subgroupOf_eq_of_le hMJ,
    map_subgroupOf_eq_of_le (show C.K1 ≤ C.K1 ⊔ (T : Subgroup G) from le_sup_left),Subgroup.map_bot] at hm
  exact le_bot_iff.mp ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hm.le)

/-- The reduced seed orbit makes the original point component a faithful signalizer member. -/
theorem nonabelian_point_component_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) : ChapterA.Section04.IsFaithfulSignalizerType C.K1 := by
  have hl := nonabelian_point_component_local h F C
  refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (h.source.simpleQTKE.evenCharacteristic T) hl, ?_⟩
  let J := C.K1 ⊔ (T : Subgroup G)
  let A := C.K1.subgroupOf J
  let R := (nonabelianCenterModule F L C.K1).subgroupOf J
  have hR := nonabelian_center_module_reduced h earlier F hne g hgP hgH C
  have hp : IsPPerfect 2 A :=
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hl).of_surjective
      (subgroupOfEquivOfLe (show C.K1 ≤ J from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show C.K1 ≤ J from le_sup_left)).symm.surjective
  have hbound := ChapterA.Section04.reduced_commutator_le_intrinsicModule A hl.1.subnormal hp
  intro hz
  have hzero : ChapterA.Section04.intrinsicSignalizerModule A = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    rw [←ChapterA.Section04.intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show C.K1 ≤ J from le_sup_left)]
    exact hz
  exact nonabelian_center_module_moved h earlier F hne g hgP hgH B h5 C
    (le_bot_iff.mp ((commutator_mono hR.le_reducedPSubgroup le_rfl).trans
      (hbound.trans hzero.le)))

/-- Select a genuine chosen module inside the literal seed orbit and hence inside Z(U). -/
theorem nonabelian_center_exists_chosen
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ∃ I : Subgroup G, Nonempty (ChosenModule T C.K1 I) ∧
      I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU := by
  have hl := nonabelian_point_component_local h F C
  let := Chapter1.mem_L_isPerfect hl
  have hn := (F.invariant 1).trans
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hMJ : nonabelianCenterModule F L C.K1 ≤ C.K1 ⊔ (T : Subgroup G) :=
    conjugateSpanBy_le ((inf_le_left.trans (sylowOmega_le T)).trans le_sup_right)
      (le_sup_left.trans (C.K1 ⊔ (T : Subgroup G)).le_normalizer)
  obtain ⟨I,hI,hIM⟩ := exists_chosen_le_reduced_witness hn
    ((nonabelianCenterModule F L C.K1).subgroupOf (C.K1 ⊔ (T : Subgroup G)))
    (nonabelian_center_module_reduced h earlier F hne g hgP hgH C)
    (nonabelian_center_module_moved h earlier F hne g hgP hgH B h5 C)
  rw [map_subgroupOf_eq_of_le hMJ] at hIM
  exact ⟨I,hI,hIM,hIM.trans (nonabelian_center_module_le_center h earlier F hne g hgP hgH C)⟩

/-- The faithful point component lies in a faithful maximal local member. -/
theorem nonabelian_point_exists_faithful_maximal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ∃ J : Subgroup G, C.K1 ≤ J ∧ FaithfulMaximalLocal T J := by
  have hl := nonabelian_point_component_local h F C
  have hf := nonabelian_point_component_faithful h earlier F hne g hgP hgH B h5 C
  obtain ⟨J,hJ,hKJ⟩ := Chapter1.exists_mem_LStar_ge hl
  have hJf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (h.source.simpleQTKE.evenCharacteristic T)
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C.K1).mpr ⟨hl,hf⟩) hJ.1 hKJ
  exact ⟨J,hKJ,hJ,((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T J).mp hJf).2⟩


/-- The actual returning center generates the point component by commutators. -/
theorem nonabelian_caseFive_component_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) : ⁅C.K1,conjugate F.ZU g⁆ = C.K1 := by
  let A := C.K1.subgroupOf F.H
  let D := (conjugate F.ZU g).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hDH : conjugate F.ZU g ≤ F.H := (F.conjugate_ZU_le_X g).trans
    (F.X_le_H g (F.P_le_G₂ (by decide) L h.chosen.normalizes hgP))
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h (Or.inl rfl) earlier F hne B h5
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup F.TerminalHdot := e.isSimpleGroup
  have hR : (solvableRadical F.H).map q = ⊥ := by
    let R := (solvableRadical F.H).map q
    let : R.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    apply (inferInstance : R.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let : Group.IsSolvable R := Group.isSolvable_of_surjective
      (q.subgroupMap_surjective (solvableRadical F.H))
    have htSol : Group.IsSolvable (⊤ : Subgroup F.TerminalHdot) := ht ▸ inferInstance
    let := htSol
    exact nonabelian_hat_not_solvable h (Or.inl rfl) F hne
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup F.TerminalHdot) ≃*
        F.TerminalHdot).toMonoidHom) topEquiv.surjective)
  have hnon : ¬ ⁅A,D⁆ ≤ solvableRadical F.H := by
    intro hr
    have hc := map_mono (f := q) hr
    rw [map_commutator, hR] at hc
    have ha : A.map q = ⊤ := nonabelian_caseFive_point_component_image
      h (Or.inl rfl) earlier F hne B h5 C
    rw [ha] at hc
    have hdC : D.map q ≤ center F.TerminalHdot :=
      commutator_top_left_eq_bot_iff_le_center.mp (le_bot_iff.mp hc)
    have hZ : center F.TerminalHdot = ⊥ := by
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      apply e.injective
      have hh := (centerCongr e ⟨x,hx⟩).property
      change e x ∈ center (alternatingGroup (Fin 8)) at hh
      rw [alternatingGroup.center_eq_bot (by simp)] at hh
      exact (mem_bot.mp hh).trans (map_one e).symm
    have hd : F.terminalDot (conjugate F.ZU g) = ⊥ := le_bot_iff.mp (hdC.trans hZ.le)
    exact (nonabelian_caseFive_center h (Or.inl rfl) earlier F hne g hgP hgH B h5).2 hd
  have hc := (C.component.commutator_le_radical_or_eq_iSup_conjugates D).resolve_left hnon
  let : A.Normal := C.normal
  have he : ⁅A,D⁆ = A := by
    rw [hc]
    exact le_antisymm
      (iSup_conjugates_le_of_le_normalizer A D A le_rfl
        (A.normalizer_eq_top ▸ le_top))
      (le_iSup_conjugates A D)
  have hm := congrArg (map F.H.subtype) he
  simpa only [A,D,map_commutator,map_subgroupOf_eq_of_le C.point_le,
    map_subgroupOf_eq_of_le hDH] using hm


omit [Finite G] in
private theorem chosen_not_centralized {J I : Subgroup G} (c : ChosenModule T J I) :
    ¬ J ≤ centralizer (I : Set G) := by
  intro hc
  apply c.irrPlus.isIrrPlus.not_le_fixedSpace _
  intro v hv j
  have hi : (v.toMul.val : G) ∈ I := c.image_eq.le
    (mem_map_of_mem _ (mem_map_of_mem _ hv))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (j.val.val : G) * (v.toMul.val : G) * (j.val.val : G)⁻¹ = (v.toMul.val : G)
  exact mul_inv_eq_iff_eq_mul.mpr ((hc j.property) _ hi).symm

/-- Every chosen constituent is moved by the original returning center. -/
theorem nonabelian_caseFive_chosen_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I) :
    ⁅I,conjugate F.ZU g⁆ ≠ ⊥ := by
  intro hz
  have hd : conjugate F.ZU g ≤ centralizer (I : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  apply chosen_not_centralized c
  rw [←nonabelian_caseFive_component_commutator h earlier F hne g hgP hgH B h5 C]
  exact (commutator_mono le_rfl hd).trans
    (le_normalizer_iff_commutator_le_right.mp
      (c.normalizes.trans (normalizer_le_normalizer_centralizer _)))

/-- Construct a chosen constituent inside the literal seed orbit, retaining
its nontrivial action by the same conjugate center used in equation (*). -/
theorem nonabelian_center_exists_moved_chosen
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ∃ I : Subgroup G, Nonempty (ChosenModule T C.K1 I) ∧
      I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧ ⁅I,conjugate F.ZU g⁆ ≠ ⊥ := by
  obtain ⟨I,⟨c⟩,hi,hz⟩ := nonabelian_center_exists_chosen h earlier F hne g hgP hgH B h5 C
  exact ⟨I,⟨c⟩,hi,hz,nonabelian_caseFive_chosen_moved h earlier F hne g hgP hgH B h5 C c⟩


/-- L₀-irreducibility makes every chosen constituent in Z(U) cover the
original quotient by C_{Z(U)}(Z(U)^g). -/
theorem nonabelian_caseFive_chosen_covers_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) :
    (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU := by
  let K := F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)
  have hk := nonabelian_caseFive_center_centralizer h (Or.inl rfl) earlier F hne g hgP hgH B h5
  have hRI : planeCentralizerResidual F L ≤ normalizer (I : Set G) := by
    apply le_trans (b := F.Li L 1) _ (C.contains.trans c.normalizes)
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans inf_le_left
  have hRK := nonabelian_planeResidual_normalizes_center_centralizer h earlier F g hgP
  have he := nonabelian_caseFive_center_quotient_irreducible h (Or.inl rfl) earlier F hne
    g hgP hgH B h5 (K ⊔ I) (hk.ge.trans le_sup_left) (sup_le inf_le_left hiZ)
    ((le_inf hRK hRI).trans (normalizer_inf_normalizer_le_normalizer_sup K I))
  apply he.resolve_left
  intro he
  have hIK : I ≤ K := le_sup_right.trans (he.trans hk.symm).le
  exact nonabelian_caseFive_chosen_moved h earlier F hne g hgP hgH B h5 C c
    (commutator_eq_bot_iff_le_centralizer.mpr (hIK.trans inf_le_right))

/-- The actual returning-center action has moved rank two on every chosen
constituent lying in Z(U), before its natural-module identification. -/
theorem nonabelian_caseFive_chosen_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) :
    (I ⊓ centralizer (conjugate F.ZU g : Set G)).relIndex I = 4 := by
  let K := F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)
  have he := nonabelian_caseFive_chosen_covers_center h earlier F hne g hgP hgH B h5 C c hiZ
  have hm := relIndex_sup_left (I.subgroupOf F.ZU) (K.subgroupOf F.ZU)
  rw [←subgroupOf_sup (show K ≤ F.ZU from inf_le_left) hiZ,
    relIndex_subgroupOf (sup_le inf_le_left hiZ),relIndex_subgroupOf hiZ] at hm
  have hi : I ⊓ K = I ⊓ centralizer (conjugate F.ZU g : Set G) := by
    dsimp only [K]
    rw [←inf_assoc,inf_eq_left.mpr hiZ]
  rw [←hi,inf_relIndex_left,←hm,he]
  exact nonabelian_caseFive_center_centralizer_index h (Or.inl rfl) earlier F hne g hgP hgH B h5

/-- Actual source constituent with the literal fixed-space index from (*). -/
theorem nonabelian_center_exists_rank_two_chosen
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ∃ I : Subgroup G, Nonempty (ChosenModule T C.K1 I) ∧
      I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧
      (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU ∧
      (I ⊓ centralizer (conjugate F.ZU g : Set G)).relIndex I = 4 := by
  obtain ⟨I,⟨c⟩,hi,hz⟩ := nonabelian_center_exists_chosen h earlier F hne g hgP hgH B h5 C
  exact ⟨I,⟨c⟩,hi,hz,
    nonabelian_caseFive_chosen_covers_center h earlier F hne g hgP hgH B h5 C c hz,
    nonabelian_caseFive_chosen_centralizer_index h earlier F hne g hgP hgH B h5 C c hz⟩


/-- The point component's intrinsic two-core quotient is the actual faithful
actor. The equivalence commutes with the original quotient action. -/
theorem nonabelian_caseFive_point_core_equiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ∃ e : (C.K1 ⧸ pCore 2 C.K1) ≃* F.TerminalHdot,
      ∀ k : C.K1, e (QuotientGroup.mk' (pCore 2 C.K1) k) =
        QuotientGroup.mk' F.terminalHatAction.ker (inclusion C.point_le k) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let f := q.comp (inclusion C.point_le)
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ F.terminalDot C.K1 :=
      (nonabelian_caseFive_point_component_image h (Or.inl rfl) earlier F hne B h5 C).symm ▸ mem_top y
    obtain ⟨a,ha,he⟩ := hy
    exact ⟨⟨a,ha⟩,he⟩
  have hk : pCore 2 C.K1 ≤ f.ker := by
    intro k hk
    have hh := pCoreAmbient_mono_of_isSubnormalIn C.K1 F.H 2 C.point_le
      C.normal.isSubnormal (mem_map_of_mem C.K1.subtype hk)
    obtain ⟨a,ha,he⟩ := hh
    have hea : a = inclusion C.point_le k := Subtype.ext he
    subst a
    exact (QuotientGroup.eq_one_iff _).mpr (point_core_le_hat_kernel h earlier F ha)
  let fQ := QuotientGroup.lift (pCore 2 C.K1) f hk
  have hfQ : Function.Surjective fQ :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  obtain ⟨a⟩ := nonabelian_caseFive_alternating_eight h (Or.inl rfl) earlier F hne B h5
  have hc : Nat.card F.TerminalHdot = 20160 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hq : IsQuasisimple (C.K1 ⧸ pCore 2 C.K1) := by
    by_contra hnq
    obtain ⟨⟨b⟩,K,hK,hfin,hcard,⟨e⟩⟩ := component_nonquasisimple_seven_core h F 1
      (Or.inr ⟨rfl,Or.inl rfl⟩) rfl ⟨C.point_le,C.component⟩ C.contains hnq
    have h7 : Nat.card (pCore 7 (C.K1 ⧸ pCore 2 C.K1)) = 49 := by
      rw [Nat.card_congr b.toEquiv]
      change Nat.card (Fin 2 → ZMod 7) = 49
      rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      decide
    have he : Nat.card ((C.K1 ⧸ pCore 2 C.K1) ⧸ pCore 7 (C.K1 ⧸ pCore 2 C.K1)) = 336 := by
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hcard]
      decide
    have hd := card_dvd_of_surjective fQ hfQ
    rw [hc,card_eq_card_quotient_mul_card_subgroup (pCore 7 (C.K1 ⧸ pCore 2 C.K1)),he,h7] at hd
    exact (by decide : ¬20160 ∣ 336*49) hd
  let := hq
  have hi := AlternatingEight.reduced_cover_injective (a.toMonoidHom.comp fQ)
    (a.surjective.comp hfQ) (pCore_quotient_pCore_eq_bot 2)
  refine ⟨MulEquiv.ofBijective fQ ⟨?_,hfQ⟩,fun _ => rfl⟩
  exact fun x y he => hi (congrArg a he)

/-- The PSL₄(2) premise of NaturalReduction is now supplied by the original
point action and its exact two-core quotient. -/
theorem nonabelian_caseFive_point_core_model
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 := by
  obtain ⟨e,_⟩ := nonabelian_caseFive_point_core_equiv h earlier F hne B h5 C
  obtain ⟨a⟩ := nonabelian_caseFive_alternating_eight h (Or.inl rfl) earlier F hne B h5
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨(e.trans a).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩


/-- Apply the seed construction and action transport to the point component
constructed from the original source hypotheses. Maximality, the natural-module
identification and the final parabolic contradiction remain to be proved. -/
theorem nonabelian_caseFive_constituent_data
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ C : ComponentGeometry F L,
      ChapterA.Section04.IsFaithfulSignalizerType C.K1 ∧
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∧
      IsPReduced 2 ((nonabelianCenterModule F L C.K1).subgroupOf (C.K1 ⊔ (T : Subgroup G))) ∧
      ∃ I : Subgroup G, Nonempty (ChosenModule T C.K1 I) ∧
        I ≤ nonabelianCenterModule F L C.K1 ∧ I ≤ F.ZU ∧
        (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) ⊔ I = F.ZU ∧
        (I ⊓ centralizer (conjugate F.ZU g : Set G)).relIndex I = 4 := by
  obtain ⟨C⟩ := componentGeometry earlier h (Or.inl rfl) F
  exact ⟨C,
    nonabelian_point_component_faithful h earlier F hne g hgP hgH B h5 C,
    nonabelian_caseFive_point_core_model h earlier F hne B h5 C,
    nonabelian_center_module_reduced h earlier F hne g hgP hgH C,
    nonabelian_center_exists_rank_two_chosen h earlier F hne g hgP hgH B h5 C⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
