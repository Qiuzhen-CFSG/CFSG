module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Assembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceQuotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceResiduals.ImageAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.SourceOrientation
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction

/-!
# Source residual geometry before centre identification

The marked source branch constructs the oriented Borel planes and forces
n=2. The centralizing plane gives Y₊=Y. The full extraspecial alternative
is then excluded by its centre-preimage equation, so the full natural-action
constructor and residual identification apply. Finally image generation
and the two-group action kernel transfer the original outer diagonal action
to the opposite residual, in exactly the same projective marking.

`PreparedResiduals` is an output of this construction. It assumes neither
RankTwoDiagonal nor Y₊=A⟨y⟩, and the theorem below uses neither the disputed
kernel action nor any later centre, centralizer or full-product conclusion.
The subsequent intrinsic root and central-cover lifting arguments are still
needed to identify the centre and the local centralizers.

Source: Aschbacher--Smith, genuine earlier conclusions 15.3.2--12/25/33/36
and proof of 15.3.38, combined manuscript (1 March 2004), printed p.1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- Constructed residual geometry in the originally supplied marking.
The fields do not assert a component centre or centralizer identity. -/
structure PreparedResiduals (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    {n : ℕ} (c : ProjectiveMarking L (2 ^ n)) (y : d.Yplus) where
  borel : OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c
  parameter : n = 2
  plus : d.Yplus = d.Y
  normal : (L.subgroupOf I).Normal
  normalizes : d.Yplus ≤ normalizer (L : Set G)
  elementary : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V
  quotient_card : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9
  residual : ResidualPlaneData d.M d.Y d.Yplus L borel.W₁ borel.W₂
  opposite_quotient : Nat.card (planeResidual d.M d.Y borel.W₂ ⧸
    pCore 2 (planeResidual d.M d.Y borel.W₂)) = 3
  opposite_diagonal : ∃ z ∈ planeResidual d.M d.Y borel.W₂, c.Diagonal z
  image_generation : (quotientAction normalizes c.equivalence).range ≤
    ((componentPart d.Yplus L).subgroupOf d.Yplus).map
      (quotientAction normalizes c.equivalence) ⊔
    zpowers (quotientAction normalizes c.equivalence y)
  kernel : (quotientAction normalizes c.equivalence).ker ≤ pCore 2 d.Yplus

/-- All source Borel, residual and image-generation premises are discharged.
Only the selected marked branch and exact earlier local conclusions enter. -/
theorem preparedResiduals_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L) (e : SourceBorel.Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hcase : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Nonempty (PreparedResiduals d I L c y) := by
  obtain ⟨b⟩ := SourceBorel.orientedBorelData_of_marked_source h.outside h.component_le
    h.component h.rank_component h.rank_yplus e hn heven c y.property hy
  have hn2 := parameter_eq_two_of_root c hn heven
    (b.second_le_component_sylow.trans inf_le_right) b.second_card b.root
  have hplus := b.yplus_eq_y d.choice hcase h.component_outside
  have hnormal := rank_two_component_normal_in h.component_le h.component h.odd_core
    h.rank_overgroup h.rank_component
  have hIL := (normal_subgroupOf_iff_le_normalizer h.component_le).mp hnormal
  have hYplusI : d.Yplus ≤ I := le_sup_left.trans h.outside.1.2
  have hYL : d.Yplus ≤ normalizer (L : Set G) := hYplusI.trans hIL
  have hYL' : d.Y ≤ normalizer (L : Set G) := hplus.ge.trans hYL
  have hE := b.elementaryAlternative hplus hYL' h.quotient_three h7
  obtain ⟨e9⟩ := hE.2.1
  have h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9 := by
    rw [Nat.card_congr e9.toEquiv]
    simp [ThreeAlternatives.ElementaryNine, Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := RankTwo.planeActorPair_of_fullAction d.action d.T d.sylow_le
    (localModule_le d.T d.sylow_le) himage7 h9
  have r := SourceResiduals.of_localData d b hplus h.outside h.component_le hnormal h9 a ha
  let A := componentPart d.Yplus L
  let D := planeResidual d.M d.Y b.W₂
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hMt : d.M.map (MulAut.conj b.t).toMonoidHom = d.M :=
    mem_normalizer_iff_map_conj_eq.mp (d.M.le_normalizer b.t_mem)
  have hYt : d.Y.map (MulAut.conj b.t).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp (hMY b.t_mem)
  have hAD : A.map (MulAut.conj b.t).toMonoidHom = D := by
    change (componentPart d.Yplus L).map _ = _
    rw [r.component_eq, planeResidual_map, hMt, hYt, b.first_interchange]
  let eAD : A ≃* D := ((MulAut.conj b.t).subgroupMap A).trans (MulEquiv.subgroupCongr hAD)
  have hDquot : Nat.card (D ⧸ pCore 2 D) = 3 :=
    (Nat.card_congr (QuotientGroup.congr (pCore 2 A) (pCore 2 D)
      eAD (pCore_map_iso 2 eAD)).toEquiv).symm.trans b.component_quotient
  have hYW : d.Y ≤ normalizer (b.W₂ : Set G) := by
    rcases b.planes with ⟨_, h₂⟩ | ⟨_, h₂⟩
    · rw [h₂]
      exact RankTwo.perfect_normalizes_planes d.action hYM (residualY_isPPerfect _ _) _
    · rw [h₂]
      exact RankTwo.perfect_normalizes_planes d.action hYM (residualY_isPPerfect _ _) _
  have hYD : d.Y ≤ normalizer (D : Set G) :=
    normalizes_planeResidual (hYM.trans d.M.le_normalizer) d.Y.le_normalizer hYW
  have hDY : D ≤ d.Y := (planeResidual_le _ _ _).trans inf_le_left
  have hdis := SourceResiduals.images_disjoint_of_cyclic_quotients
    (RankTwo.componentFactor_le_left d.Yplus L) (hDY.trans hplus.ge)
    (ComponentIntersection.normalizes_intersectionResidual hYL) (hplus.le.trans hYD)
    b.component_quotient hDquot (hplus.symm ▸ h9) (hplus.trans r.generated)
  obtain ⟨m, hmout, β, hβ, hcompat⟩ := hy.2
  let w : MatrixImage.DiagonalCoordinates L (y : G) c.F :=
    ⟨c.equivalence, β, m, hβ, hmout, hcompat⟩
  have hfield : Nat.card c.F = 4 := by rw [c.card, hn2]; norm_num
  have hi := MatrixImage.image_le_of_source_setup h hYL y
    ((Subgroup.orderOf_coe y).symm.trans hy.1) (Or.inr hfield) w
  have hZ := center_eq_twoCore_in h.component_le h.component h.odd_core
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  have hK := quotientAction_kernel_le_core hplus.le h.quotient_three hYplusI hYL
    c.equivalence hZ.ge (Candidates.local_centralizer_three_coprime h.component_le
      h.component h.odd_core h.rank_component.ge h.rank_overgroup)
  have hK' : (quotientAction hYL c.equivalence).ker.map d.Yplus.subtype ≤
      d.Yplus.pCoreIn 2 := hK.trans (congrArg (fun X : Subgroup G => X.pCoreIn 2) hplus.symm).le
  have hk : (quotientAction hYL c.equivalence).ker ≤ pCore 2 d.Yplus := by
    intro x hx
    obtain ⟨u, hu, he⟩ := hK' (mem_map_of_mem d.Yplus.subtype hx)
    exact (show u = x from Subtype.ext he) ▸ hu
  obtain ⟨z, hzD, hz3, _⟩ := r.outside_actor
  have hzY : z ∈ d.Yplus := hplus.ge (hDY hzD)
  have hz := SourceResiduals.diagonal_of_image_generation c hYL y hy hi hk hdis
    ⟨z, hzY⟩ hzD hz3
  exact ⟨⟨b, hn2, hplus, hnormal, hYL, hE, h9, r, hDquot, ⟨z, hzD, hz⟩, hi, hk⟩⟩

omit [Finite G] in
/-- Reindexing the deduced field order retains both diagonal actors, the
coefficient field and the exact quotient equivalence. -/
theorem PreparedResiduals.marking_four
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    {n : ℕ} {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y) (hy : c.Diagonal (y : G)) :
    ∃ hq : 2 ^ n = 4, (resizeMarking c hq).Diagonal (y : G) ∧
      ∃ z ∈ planeResidual d.M d.Y g.borel.W₂, (resizeMarking c hq).Diagonal z := by
  have hq : 2 ^ n = 4 := by rw [g.parameter]; norm_num
  exact ⟨hq, hy, g.opposite_diagonal⟩

/-- Central-omega elimination is available before lifting the projective
commutator calculation. In particular the component centre has no fixed
points under the full opposite residual. -/
theorem PreparedResiduals.center_fixed_eq_bot
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    {n : ℕ} {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y)
    (h : MatrixImage.SourceSetup d I L)
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    d.S ⊓ centralizer (d.Y : Set G) = ⊥ ∧
    centerImage L ⊓ centralizer (planeResidual d.M d.Y g.borel.W₂ : Set G) = ⊥ := by
  obtain ⟨P, hP⟩ := h.sylow
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hCS := sylow_centralizer_eq_bot d.S d.Y d.V
    (hP ▸ P.isPGroup'.map I.subtype) (hSM.trans hMY) hΩ hVY
  have hIL := (normal_subgroupOf_iff_le_normalizer h.component_le).mp g.normal
  have hZ := center_eq_twoCore_in h.component_le h.component h.odd_core
  have hZS : centerImage L ≤ d.S := by
    have he : centerImage L = L.pCoreIn 2 := congrArg (Subgroup.map L.subtype) hZ
    rw [he]
    exact (pCoreIn_mono_of_normalizes h.component_le hIL).trans
      (hP ▸ pCoreIn_le_sylow I P)
  refine ⟨hCS, le_bot_iff.mp ?_⟩
  intro z hz
  apply hCS.le
  refine ⟨hZS hz.1, ?_⟩
  rw [g.residual.generated, centralizer_join]
  refine ⟨?_, hz.2⟩
  exact centralizer_le (show componentPart d.Yplus L ≤ L from
    (map_subtype_le _).trans inf_le_right) (centerImage_centralizes L hz.1)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
