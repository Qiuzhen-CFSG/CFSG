module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.ChiefCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Residual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualAction

/-!
# The moving plane and the central-omega obstruction

Once the actual component residuals are identified with the two residual
plane centralizers, the cubic coordinate calculation determines
U = [V,Y_L] and its complementary definite plane without relabeling LocalData.
It gives order four, S-invariance, Y_C-fixation and trivial Y_L-fixed subgroup.
Conjugation by every element of T outside S exchanges the residuals.

Independently, the elementary span and preliminary core bounds place U in
Z([O₂(L),L]). Transport to any of the first three actual C.1.34 natural layers
retains its binary dimension two and the same component quotient marking.
For case (5), a nontrivial normal elementary subgroup of S meets Ω₁(Z(S));
its asserted centrality contradicts the trivial Y_L-fixed subgroup on U.
Thus the fifth-case obstruction needs no assumed position of a line.

ResidualPlaneFactors is an intermediate conclusion, not a source hypothesis.
This module does not construct it or prove the source S-normalization and
second-choice exclusion. Those obligations belong to the residual action
reductions assembled by Geometry. No total-order-three assertion is made.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.23, printed pp.1128–1129; C.1.34, printed pp.136–137.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
open CFSG.Quasithin.Chapter15.Section03.RankTwo
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
variable {G : Type*} [Group G]

/-- The actual moving subgroup in 15.3.23, before choosing its orientation. -/
noncomputable abbrev movingPlane (d : LocalData G) (L : Subgroup G) : Subgroup G :=
  ⁅d.V, YL d L⁆

/-- The residual identification still to be proved from the source quotient
actions. Neither orientation is preferred. This is an intermediate conclusion,
not an additional hypothesis of the source theorem. -/
def ResidualPlaneFactors (d : LocalData G) (L : Subgroup G) : Prop :=
  ∃ i j : OrthogonalPlaneIndex, i ≠ j ∧
    YL d L = centralizingFactor d.Y (d.action.plane i) ∧
    YC d L = centralizingFactor d.Y (d.action.plane j)

private theorem plane_map_conjugation [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (m : M) (i : OrthogonalPlaneIndex) :
    (d.plane i).map (MulAut.conj (m : G)).toMonoidHom =
      d.plane ((d.actor m).right * i) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply eq_of_le_of_card_ge
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hv
    change d.coordinates v ∈ orthogonalCoordinatePlane i at hv
    let w : V := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v
    refine mem_map.mpr ⟨w, ?_, rfl⟩
    change d.coordinates w ∈ orthogonalCoordinatePlane ((d.actor m).right * i)
    rw [show d.coordinates w = d.actor m • d.coordinates v from d.compatible m v]
    intro k hk
    have hki : (d.actor m).right⁻¹ * k ≠ i := by
      intro h
      exact hk (inv_mul_eq_iff_eq_mul.mp h)
    change (d.actor m).left k • d.coordinates v ((d.actor m).right⁻¹ * k) = 1
    rw [hv _ hki, smul_one]
  · rw [d.card_plane, card_map_of_injective (MulAut.conj (m : G)).injective,
      d.card_plane]

/-- An element of T outside S exchanges both definite coordinate planes. -/
theorem outside_S_exchanges_planes [Finite G] (d : LocalData G)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    (d.action.plane i).conjBy t = d.action.plane j := by
  let m : d.M := ⟨t, d.sylow_le ht⟩
  have hshift : (d.action.actor m).right ≠ 1 := by
    intro h
    apply htS
    refine ⟨ht, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    change (d.action.plane 1).map (MulAut.conj (m : G)).toMonoidHom = _
    rw [plane_map_conjugation, h, one_mul]
  have he : (d.action.actor m).right * i = j := by
    have h : ∀ a i j : OrthogonalPlaneIndex, a ≠ 1 → i ≠ j → a * i = j := by decide
    exact h _ i j hshift hij
  change (d.action.plane i).map (MulAut.conj (m : G)).toMonoidHom = _
  rw [plane_map_conjugation, he]

/-- The identified residual directions are exchanged by every element of
T outside S; the equality uses conjugation of the actual residual centralizers. -/
theorem residual_factors_exchanged [Finite G] (d : LocalData G) (L : Subgroup G)
    (hf : ResidualPlaneFactors d L)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    (YL d L).conjBy t = YC d L := by
  obtain ⟨i, j, hij, hL, hC⟩ := hf
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp (residualY_normal _ _)
  have hY : d.Y.map (MulAut.conj t).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp (hMY (d.sylow_le ht))
  change (YL d L).map (MulAut.conj t).toMonoidHom = _
  rw [hL, hC, centralizingFactor_map, hY,
    show (d.action.plane i).map (MulAut.conj t).toMonoidHom = d.action.plane j from
      outside_S_exchanges_planes d hij t ht htS]

private theorem four_group_fixed_trivial (U A : Subgroup G) [IsKleinFour U]
    (hA : IsPPerfect 2 A) (hmove : ⁅U, A⁆ = U) :
    U ⊓ centralizer (A : Set G) = ⊥ := by
  have hn : A ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  apply eq_bot_iff.mpr
  rintro u ⟨hu, huc⟩
  apply mem_bot.mpr
  by_contra hne
  let ρ : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hn)
  have he : ρ = 1 := IsKleinFour.action_eq_one_of_twoPerfect_of_fixed_ne_one ρ hA
    (show (⟨u, hu⟩ : U) ≠ 1 from fun h => hne (congrArg Subtype.val h)) (by
      intro a
      apply Subtype.ext
      change (a : G) * u * (a : G)⁻¹ = u
      rw [huc a a.property, mul_assoc, mul_inv_cancel, mul_one])
  have hc : U ≤ centralizer (A : Set G) := by
    intro v hv a ha
    have hh := congrArg (fun f : A →* MulAut U => f ⟨a, ha⟩ ⟨v, hv⟩) he
    have hh' : a * v * a⁻¹ = v := congrArg Subtype.val hh
    exact mul_inv_eq_iff_eq_mul.mp hh'
  have hb : U = ⊥ := hmove.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc)
  exact hne (hb.le hu)

/-- A nontrivial normal elementary subgroup of S meets its central omega
subgroup. Hence a fixed-point-free actor on that subgroup cannot centralize
the whole central omega subgroup. -/
theorem centralOmega_not_le_centralizer [Finite G] (S U A : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hn : S ≤ normalizer (U : Set G)) (hne : U ≠ ⊥)
    (hfixed : U ⊓ centralizer (A : Set G) = ⊥) :
    ¬ Stellmacher.omegaOneCenterAmbient S ≤ centralizer (A : Set G) := by
  intro hcentral
  let N := U.subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial U := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hUS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨u, hune, huZ⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  have huO : ((u : S) : G) ∈ Stellmacher.omegaOneCenterAmbient S := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff S _).mpr
    refine ⟨(u : S).property, elemPow_eq_one_of_isElementaryAbelian _ u.property, ?_⟩
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp huZ ⟨s, hs⟩)
  have hu1 : ((u : S) : G) = 1 := hfixed.le
    (show ((u : S) : G) ∈ U ⊓ centralizer (A : Set G) from ⟨u.property, hcentral huO⟩)
  exact hune (Subtype.ext (Subtype.ext hu1))

/-- The subgroup is a definite plane, with the complementary plane identified
at the same time. The cubic commutator computations use the actual action. -/
theorem movingPlane_coordinates [Finite G] (d : LocalData G) (L : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L) :
    ∃ i j : OrthogonalPlaneIndex, i ≠ j ∧
      movingPlane d L = d.action.plane j ∧
      ⁅d.V, YC d L⁆ = d.action.plane i ∧
      ⁅movingPlane d L, YL d L⁆ = movingPlane d L ∧
      movingPlane d L ⊔ d.action.plane i = d.V ∧
      Disjoint (movingPlane d L) (d.action.plane i) := by
  obtain ⟨i, j, hij, hL, hC⟩ := hf
  have hc := residualY_fullActionCoordinateFacts d.action h7
  have hm : movingPlane d L = d.action.plane j := by
    change ⁅d.V, YL d L⁆ = _
    rw [hL]
    exact hc.commutator i j hij
  refine ⟨i, j, hij, hm, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    exact hc.commutator j i hij.symm
  · rw [hm, hL]
    exact hc.commutator_self i j hij
  · rw [hm]
    exact natural_planes_sup d.action hij.symm
  · rw [hm]
    exact natural_planes_disjoint d.action hij.symm

/-- The derived plane has order four, is S-invariant, is centralized by the
other residual, and has no nonidentity Y_L-fixed point. -/
theorem movingPlane_geometry [Finite G] (d : LocalData G) (L : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L) :
    Nat.card (movingPlane d L) = 4 ∧ movingPlane d L ≤ d.S ∧
      d.S ≤ normalizer (movingPlane d L : Set G) ∧
      YC d L ≤ centralizer (movingPlane d L : Set G) ∧
      movingPlane d L ⊓ centralizer (YL d L : Set G) = ⊥ := by
  obtain ⟨i, j, hij, hL, hC⟩ := hf
  have hm : movingPlane d L = d.action.plane j := by
    change ⁅d.V, YL d L⁆ = _
    rw [hL]
    exact (residualY_fullActionCoordinateFacts d.action h7).commutator i j hij
  have hUV : movingPlane d L ≤ d.V := hm ▸ d.action.plane_le j
  have hmove : ⁅movingPlane d L, YL d L⁆ = movingPlane d L := by
    rw [hm, hL]
    exact (residualY_fullActionCoordinateFacts d.action h7).commutator_self i j hij
  have hcard : Nat.card (movingPlane d L) = 4 := hm ▸ d.action.card_plane j
  let _ := d.action.elementary_of_le hUV
  let _ : Nontrivial (movingPlane d L) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let _ : IsKleinFour (movingPlane d L) :=
    ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  refine ⟨hcard, hUV.trans (d.action.le_planeStabilizer d.T d.sylow_le
    (localModule_le d.T d.sylow_le) 1), ?_, ?_, ?_⟩
  · rw [hm]
    exact planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 j
  · rw [hm, hC]
    exact centralizingFactor_le _ _
  · exact four_group_fixed_trivial _ _
      (ComponentIntersection.intersectionResidual_isPPerfect _ _) hmove

/-- The source subgroup Y_L S_L acts on the moving plane. Its parabolic
identification comes from the earlier C.2.7 conclusion, with this same action. -/
theorem componentParabolic_normalizes_movingPlane [Finite G]
    (d : LocalData G) (L : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L) :
    YL d L ⊔ (d.S ⊓ L) ≤ normalizer (movingPlane d L : Set G) :=
  sup_le (normalizer_commutator_ge_right d.V (YL d L))
    (inf_le_left.trans (movingPlane_geometry d L h7 hf).2.2.1)

/-- Both residuals are invariant under Y₊S after identifying the literal
residual plane centralizers. The source proof must establish that identification. -/
theorem identified_residual_factors_normalized [Finite G]
    (d : LocalData G) (L : Subgroup G) (hf : ResidualPlaneFactors d L) :
    d.Yplus ⊔ d.S ≤ normalizer (YL d L : Set G) ∧
      d.Yplus ⊔ d.S ≤ normalizer (YC d L : Set G) := by
  have hYM : d.Yplus ≤ d.M := (yplus_le_residualY_of_choice d.choice).trans
    (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp (residualY_normal _ _)
  have hHY : d.Yplus ⊔ d.S ≤ normalizer (d.Y : Set G) :=
    (sup_le hYM (inf_le_left.trans d.sylow_le)).trans hMY
  have hn (i : OrthogonalPlaneIndex) :
      d.Yplus ⊔ d.S ≤ normalizer (d.action.plane i : Set G) :=
    sup_le (perfect_normalizes_planes d.action hYM (yplus_perfect_of_choice d.choice) i)
      (planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 i)
  obtain ⟨i, j, _, hL, hC⟩ := hf
  rw [hL, hC]
  exact ⟨normalizes_centralizingFactor hHY (hn i), normalizes_centralizingFactor hHY (hn j)⟩

/-- The actual residual directions generate Y; the kernel comparison uses
the genuine order-nine two-core quotient, not the total order of Y. -/
theorem identified_residual_factors_generate [Finite G]
    (d : LocalData G) (L : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9)
    (hf : ResidualPlaneFactors d L) : d.Y = YL d L ⊔ YC d L := by
  obtain ⟨i, j, hij, hL, hC⟩ := hf
  have hc := residualY_fullActionCoordinateFacts d.action h7
  rw [hL, hC]
  exact residual_plane_generation_of_images d.action hij h7 h9 (hc.image_card i) (hc.image_card j)

/-- The generated original residual is contained in Y₊, so the reverse
containment supplied by either source choice forces equality. -/
theorem identified_Yplus_eq_Y [Finite G] (d : LocalData G) (L : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9)
    (hf : ResidualPlaneFactors d L) : d.Yplus = d.Y := by
  apply le_antisymm (yplus_le_residualY_of_choice d.choice)
  change d.Y ≤ d.Yplus
  rw [identified_residual_factors_generate d L h7 h9 hf]
  exact sup_le ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left)
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left)

/-- The residual normalizer calculation applies to the identified factors.
This reuses the exact section-centralizer residual, including its two-core. -/
theorem identified_YC_normalizer_not_le_M [Finite G] (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hf : ResidualPlaneFactors d c.L) : ¬ normalizer (YC d c.L : Set G) ≤ d.M :=
  YC_normalizer_not_le_M d c hcore hR
    (le_sup_right.trans (identified_residual_factors_normalized d c.L hf).2)

/-- The moving plane lies in the actual component core commutator and in
its center. This placement uses the elementary span and the preliminary
core bound, not a preferred coordinate label or a classified core shape. -/
theorem movingPlane_le_coreCenter [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    movingPlane d c.L ≤ CoreActions.coreCenter c.L := by
  have hUL : movingPlane d c.L ≤ spanCommutator d c.L :=
    commutator_mono (le_conjugateSpanBy d.V c.L)
      ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right)
  have hUQ := hUL.trans (spanCommutator_le_core d c hSL)
  have hYL : YL d c.L ≤ d.M :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      ((yplus_le_residualY_of_choice d.choice).trans
        (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
  have hUV : movingPlane d c.L ≤ d.V :=
    le_normalizer_iff_commutator_le_left.mp (hYL.trans d.action.normalizes)
  have hVQ : d.V ≤ centralizer (commutatorCore c.L : Set G) :=
    le_centralizer_iff.mp ((commutatorCore_le c.L).trans
      (hcore.trans (hR.le.trans inf_le_right)))
  intro u hu
  exact mem_map.mpr ⟨⟨u, hUQ hu⟩, mem_center_iff.mpr (fun q =>
    Subtype.ext ((hVQ (hUV hu)) q q.property)), rfl⟩

/-- Any actual local realization of case (5) contradicts the derived plane.
The hypothesis identifies the embedded Sylow and component; the full FifthCase
retains its natural quotient, common action marking and index-seven clause. -/
theorem fifthCase_impossible_of_residual_factors [Finite G] (d : LocalData G)
    (L H : Subgroup G) (hLH : L ≤ H) (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = d.S)
    (R : Subgroup H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L)
    (hfive : FifthCase (L.subgroupOf H) R P e) : False := by
  obtain ⟨hc, hUS, hn, _, hfix⟩ := movingPlane_geometry d L h7 hf
  have hYL : YL d L ≤ L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hYM : YL d L ≤ d.M :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      ((yplus_le_residualY_of_choice d.choice).trans
        (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
  have hUV : movingPlane d L ≤ d.V :=
    le_normalizer_iff_commutator_le_left.mp (hYM.trans d.action.normalizes)
  let _ := d.action.elementary_of_le hUV
  have hne : movingPlane d L ≠ ⊥ := by intro h; rw [h] at hc; norm_num at hc
  apply centralOmega_not_le_centralizer d.S (movingPlane d L) (YL d L)
    (d.T.isPGroup'.to_le inf_le_left) hUS hn hne hfix
  have hO : Stellmacher.omegaOneCenterAmbient d.S =
      (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)).map H.subtype := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hP]
  rw [hO]
  rintro u ⟨x, hx, rfl⟩ a ha
  exact congrArg Subtype.val (mem_center_iff.mp (hfive.central_omega hx)
    ⟨a, hLH (hYL ha)⟩)

/-- The actual moving subgroup in the coordinates of a natural layer. The
same quotient marking e is used for the layer and every actor below. -/
noncomputable def naturalPlaneSpace (d : LocalData G) {L A : Subgroup G} {a : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel L A ⊥ e (NaturalCopies (ZMod 2) a)) :
    Submodule (ZMod 2) (Fin a → Fin 3 → ZMod 2) :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
    (((movingPlane d L).subgroupOf A).map m.upperIso.toMonoidHom))

/-- The natural coordinates preserve the four elements of the moving plane. -/
theorem naturalPlaneSpace_card [Finite G] (d : LocalData G) {L A : Subgroup G} {a : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel L A ⊥ e (NaturalCopies (ZMod 2) a))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L) (hUA : movingPlane d L ≤ A) :
    Nat.card (naturalPlaneSpace d m) = 4 := by
  change Nat.card (((movingPlane d L).subgroupOf A).map m.upperIso.toMonoidHom) = 4
  rw [card_map_of_injective m.upperIso.injective,
    Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv]
  exact (movingPlane_geometry d L h7 hf).1

/-- The source projective line has binary dimension two. -/
theorem naturalPlaneSpace_finrank [Finite G] (d : LocalData G) {L A : Subgroup G} {a : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel L A ⊥ e (NaturalCopies (ZMod 2) a))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L) (hUA : movingPlane d L ≤ A) :
    Module.finrank (ZMod 2) (naturalPlaneSpace d m) = 2 := by
  have hc := naturalPlaneSpace_card d m h7 hf hUA
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (show 2 ^ _ = 2 ^ 2 from hc)

/-- The actual quotient image of Y_L S_L preserves the two-dimensional
subspace in this very natural model, not in an independently chosen action. -/
theorem naturalPlaneSpace_invariant [Finite G] (d : LocalData G)
    {L A : Subgroup G} {a : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel L A ⊥ e (NaturalCopies (ZMod 2) a))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L)
    (l : L) (hl : (l : G) ∈ YL d L ⊔ (d.S ⊓ L))
    (v : Fin a → Fin 3 → ZMod 2) (hv : v ∈ naturalPlaneSpace d m) :
    NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v ∈ naturalPlaneSpace d m := by
  change Multiplicative.ofAdd v ∈
    ((movingPlane d L).subgroupOf A).map m.upperIso.toMonoidHom at hv
  obtain ⟨u, hu, he⟩ := hv
  change m.upperIso u = Multiplicative.ofAdd v at he
  change Multiplicative.ofAdd _ ∈
    ((movingPlane d L).subgroupOf A).map m.upperIso.toMonoidHom
  refine mem_map.mpr ⟨layerConjugate L A m.normalized l u, ?_, ?_⟩
  · exact ((componentParabolic_normalizes_movingPlane d L h7 hf hl) u).mp hu
  · have hh := m.upperIso_intertwining l u
    rw [he] at hh
    exact congrArg Multiplicative.ofAdd hh

/-- The natural model has no fixed vector on this line for the actual Y_L
quotient action. This also certifies that the plane was not collapsed in transport. -/
theorem naturalPlaneSpace_fixed_trivial [Finite G] (d : LocalData G)
    {L A : Subgroup G} {a : ℕ}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel L A ⊥ e (NaturalCopies (ZMod 2) a))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d L)
    (v : Fin a → Fin 3 → ZMod 2) (hv : v ∈ naturalPlaneSpace d m)
    (hfix : ∀ l : L, (l : G) ∈ YL d L →
      NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v = v) : v = 0 := by
  change Multiplicative.ofAdd v ∈
    ((movingPlane d L).subgroupOf A).map m.upperIso.toMonoidHom at hv
  obtain ⟨u, hu, he⟩ := hv
  change m.upperIso u = Multiplicative.ofAdd v at he
  have hc : (u : G) ∈ centralizer (YL d L : Set G) := by
    intro l hl
    have hlL : l ∈ L := (ComponentIntersection.intersectionResidual_le _ _ hl).2
    have hh := m.upperIso_intertwining ⟨l, hlL⟩ u
    rw [he] at hh
    have hh := hh.trans (hfix ⟨l, hlL⟩ hl)
    have hh' := m.upperIso.injective (show
      m.upperIso (layerConjugate L A m.normalized ⟨l, hlL⟩ u) = m.upperIso u from
        (congrArg Multiplicative.ofAdd hh).trans he.symm)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh')
  have hu1 : (u : G) = 1 := (movingPlane_geometry d L h7 hf).2.2.2.2.le ⟨hu, hc⟩
  have hu' : u = 1 := Subtype.ext hu1
  have hv1 : Multiplicative.ofAdd v = 1 := he.symm.trans (hu' ▸ m.upperIso.map_one)
  exact congrArg Multiplicative.toAdd hv1

/-- In each of the first three source alternatives, use its actual natural
layer (Q in cases (1),(2), Z(Q) in case (3)). The core-center calculation
supplies the line containment; no line-placement premise is required. -/
theorem naturalPlaneSpace_source_geometry [Finite G] (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    {A : Subgroup G} {a : ℕ}
    (hA : A = commutatorCore c.L ∨ A = CoreActions.coreCenter c.L)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L A ⊥ e (NaturalCopies (ZMod 2) a))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d c.L) :
    movingPlane d c.L ≤ A ∧ Module.finrank (ZMod 2) (naturalPlaneSpace d m) = 2 ∧
      (∀ (l : c.L), (l : G) ∈ YL d c.L ⊔ (d.S ⊓ c.L) →
        ∀ v ∈ naturalPlaneSpace d m,
          NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v ∈ naturalPlaneSpace d m) ∧
      (∀ v ∈ naturalPlaneSpace d m,
        (∀ l : c.L, (l : G) ∈ YL d c.L →
          NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v = v) → v = 0) := by
  have hUC := movingPlane_le_coreCenter d c hSL hcore hR
  have hUA : movingPlane d c.L ≤ A := by
    rcases hA with rfl | rfl
    · exact hUC.trans (map_subtype_le _)
    · exact hUC
  exact ⟨hUA, naturalPlaneSpace_finrank d m h7 hf hUA,
    naturalPlaneSpace_invariant d m h7 hf, naturalPlaneSpace_fixed_trivial d m h7 hf⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
end
