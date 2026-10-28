module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourRadical

/-!
# The intrinsic fixed four is the complementary orthogonal plane

Every elementary four-group H in S normalized by Y₊S lies in V in the
first-choice configuration. The two-group center theorem gives a nonidentity
point of H in Ω₁Z(S), hence in V by 15.3.8. The intersection H ∩ V cannot
have order two: its Y₊-invariance would give a residual-fixed vector in V.
Thus the whole H lies in V.

Apply this to C_[O₂(L),L](L). The moving plane has no Y_L-fixed point and
the complementary plane is fixed by Y_L, so the intrinsic four is exactly
[V,Y_C]. Consequently all of V lies in [O₂(L),L], and an element of T
outside S exchanges the intrinsic four with the moving plane. These are
original-source action constraints; fixation by O₂(LS) remains separate.

Source: Aschbacher--Smith 15.3.8, 15.3.12 and 15.3.23, printed
pp.1123--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases
open CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- A residual-and-S-invariant four-group in S is contained in the original V. -/
theorem normalized_four_le_module (d : LocalData G)
    (hfirst : d.Yplus = d.Y)
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (H : Subgroup G) [IsElementaryAbelian 2 H] (hcard : Nat.card H = 4)
    (hHS : H ≤ d.S) (hH : d.Yplus ⊔ d.S ≤ normalizer (H : Set G)) :
    H ≤ d.V := by
  let N := H.subgroupOf d.S
  let : N.Normal := normal_subgroupOf_of_le_normalizer (le_sup_right.trans hH)
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial N := (subgroupOfEquivOfLe hHS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 d.S) := ⟨d.T.isPGroup'.to_le inf_le_left⟩
  obtain ⟨u, hune, huZ⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  have huO : ((u : d.S) : G) ∈ centralOmegaIn d.S := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff d.S _).mpr
    refine ⟨(u : d.S).property, elemPow_eq_one_of_isElementaryAbelian _ u.property, ?_⟩
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp huZ ⟨s, hs⟩)
  have huV : ((u : d.S) : G) ∈ d.V := by
    rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1] at huO
    exact huO.1
  let A := H ⊓ d.V
  have hAne : A ≠ ⊥ := by
    intro hb
    have hu1 : ((u : d.S) : G) = 1 := hb.le ⟨u.property, huV⟩
    exact hune (Subtype.ext (Subtype.ext hu1))
  have hdiv : Nat.card A ∣ 4 := by
    rw [← hcard]
    exact card_dvd_of_le (show A ≤ H from inf_le_left)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hAone : Nat.card A ≠ 1 := fun hc => hAne (card_eq_one.mp hc)
  have hAtwo : Nat.card A ≠ 2 := by
    intro hc
    have hYM : d.Yplus ≤ d.M := by
      rw [hfirst]
      exact Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
    have hn : d.Yplus ≤ normalizer (A : Set G) :=
      (le_inf (le_sup_left.trans hH) (hYM.trans d.action.normalizes)).trans
        inf_normalizer_le_normalizer_inf
    have hcen : A ≤ centralizer (d.Yplus : Set G) :=
      le_centralizer_iff.mp (hn.trans (normalizer_le_centralizer_of_card_two A hc))
    have hzero : fixedPlane d.V d.Yplus = ⊥ := by
      rw [hfirst]
      exact d.action.fixedPlane_eq_bot_of_residual_image
        (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) himage
    exact hAne (le_bot_iff.mp (hzero ▸ le_inf inf_le_right hcen))
  have hAthree : Nat.card A ≠ 3 := by
    intro hc
    rw [hc] at hdiv
    norm_num at hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have heq : A = H := eq_of_le_of_card_ge inf_le_left (by omega)
  exact heq ▸ inf_le_right


omit [Finite G] in
private theorem fixed_complement (U W A : Subgroup G)
    (hcomm : W ≤ centralizer (U : Set G))
    (hfixed : U ⊓ centralizer (A : Set G) = ⊥)
    (hW : W ≤ centralizer (A : Set G)) :
    (U ⊔ W) ⊓ centralizer (A : Set G) = W := by
  apply le_antisymm ?_ (le_inf le_sup_right hW)
  rintro x ⟨hx, hxc⟩
  have hxprod : x ∈ (U : Set G) * (W : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U W
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
    exact hx
  obtain ⟨u, hu, w, hw, rfl⟩ := hxprod
  have huc : u ∈ centralizer (A : Set G) :=
    (centralizer (A : Set G)).mul_mem_cancel_right (hW hw) |>.mp hxc
  have hu1 : u = 1 := hfixed.le ⟨hu, huc⟩
  simpa only [hu1, one_mul] using (show w ∈ W from hw)

/-- The actual component-fixed four is the complementary definite plane,
with its original residual labeling retained. -/
theorem coreFixed_eq_complementary_plane (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    [IsElementaryAbelian 2 (coreFixed L)] (hcard : Nat.card (coreFixed L) = 4) :
    coreFixed L = ⁅d.V, YC d L⁆ := by
  have hHV : coreFixed L ≤ d.V := normalized_four_le_module d hg.first_choice
    h.image (coreFixed L) hcard
    (inf_le_left.trans (commutatorCore_le_S d L h.core_le h.radical))
    ((sup_le h.normalizes_component hg.component_normalized).trans
      (Extension.SourceCases.FixedFour.coreFixed_normalized L))
  obtain ⟨i, j, hij, hL, hC⟩ := hg.factors
  have hm : movingPlane d L = d.action.plane j := by
    change ⁅d.V, YL d L⁆ = _
    rw [hL]
    exact (residualY_fullActionCoordinateFacts d.action h.image).commutator i j hij
  have hc : ⁅d.V, YC d L⁆ = d.action.plane i := by
    rw [hC]
    exact (residualY_fullActionCoordinateFacts d.action h.image).commutator j i hij.symm
  have hW : d.action.plane i ≤ centralizer (YL d L : Set G) := by
    rw [hL]
    exact le_centralizer_iff.mp (centralizingFactor_le _ _)
  have hcomm : d.action.plane i ≤ centralizer (movingPlane d L : Set G) := by
    let _ := d.action.elementary
    exact (d.action.plane_le i).trans
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (hm ▸ d.action.plane_le j)))
  have hsup : movingPlane d L ⊔ d.action.plane i = d.V := by
    rw [hm]
    exact natural_planes_sup d.action hij.symm
  have hfix : d.V ⊓ centralizer (YL d L : Set G) = d.action.plane i :=
    hsup ▸ fixed_complement (movingPlane d L) (d.action.plane i) (YL d L)
      hcomm hg.plane_fixed hW
  rw [hc]
  apply eq_of_le_of_card_ge
  · rw [← hfix]
    exact le_inf hHV (inf_le_right.trans (centralizer_le
      ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right)))
  · rw [d.action.card_plane, hcard]



/-- In the original component application, both definite planes now lie in
the intrinsic commutator core. -/
theorem module_le_commutatorCore_of_coreFixed_four (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    [IsElementaryAbelian 2 (coreFixed c.L)] (hcard : Nat.card (coreFixed c.L) = 4) :
    d.V ≤ commutatorCore c.L := by
  obtain ⟨i, _, _, _, hc, _, hsup, _⟩ := hg.coordinates
  have hfixed : coreFixed c.L = d.action.plane i :=
    (coreFixed_eq_complementary_plane d c.L e h hg hcard).trans hc
  rw [← hsup, ← hfixed]
  exact sup_le ((movingPlane_le_coreCenter d c hg.component_normalized
    h.core_le h.radical).trans (map_subtype_le _)) inf_le_left

/-- Conjugation outside S exchanges the actual fixed four with the moving plane. -/
theorem coreFixed_conjugate_eq_movingPlane (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    [IsElementaryAbelian 2 (coreFixed L)] (hcard : Nat.card (coreFixed L) = 4)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    (coreFixed L).conjBy t = movingPlane d L := by
  obtain ⟨i, j, hij, hm, hc, _⟩ := hg.coordinates
  rw [coreFixed_eq_complementary_plane d L e h hg hcard, hc, hm]
  exact outside_S_exchanges_planes d hij t ht htS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

