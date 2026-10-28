module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.SecondChoice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.LocalFifth
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# Assembling the residual exchange and moving-plane geometry

Starting with the earlier local conclusions and the actual marked component
parabolic, we prove invariance of both residual directions and of the component.
The second-choice centralizer residual then has normalizer M, whereas L
normalizes it, excluding that choice. The first-choice orthogonal action now
identifies the two residual factors and their exchanged definite planes.

`ResidualSourceData` contains only the earlier 15.3.7, 15.3.11–12 and C.2.7
conclusions, not residual invariance, first choice, or a moving-plane position.
The nontrivial commutator is an explicit input, to be discharged by the separate
extension argument. Elementarity of the span is the earlier 15.3.16 conclusion.
Every natural-layer calculation uses the same quotient marking as the parabolic.
The full fifth alternative is excluded inside its actual MS-group, whose Sylow
subgroup need only embed into S. The case-(4) exclusion and final L₃(2)
contradiction belong to the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.23, final paragraphs of printed p.1128; C.1.34, printed pp.136–137.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.RankTwo
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- The earlier source conclusions consumed by the residual paragraph.
The parabolic is marked through the literal quotient of L; both point and line
parabolics and their inner conjugates are allowed. Orders of residuals mean
three-parts throughout. -/
structure ResidualSourceData (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) : Prop where
  image : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  quotient_card : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9
  shadow : RankTwoShadow d.Yplus d.S
  normalizes_component : d.Yplus ≤ normalizer (L : Set G)
  component_three_part : 3 ^ (Nat.card (YL d L)).factorization 3 = 3
  centralizer_three_part : 3 ^ (Nat.card (YC d L)).factorization 3 = 3
  generation : d.Yplus = YL d L ⊔ YC d L
  core_le : L.pCoreIn 2 ≤ d.R
  radical : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)
  parabolic : ∃ (P : Subgroup Matrix.PSL3Two.SL) (g : Matrix.PSL3Two.SL),
    (P = Matrix.PSL3Two.pointParabolicSL ∨ P = Matrix.PSL3Two.lineParabolicSL) ∧
    ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = P.conjBy g

/-- Conclusions of the residual paragraph, constructed by
`residual_geometry_of_source`. In particular neither coordinate label is fixed. -/
structure ResidualGeometry (d : LocalData G) (L : Subgroup G) : Prop where
  component_residual_normalized : d.Yplus ⊔ d.S ≤ normalizer (YL d L : Set G)
  centralizer_residual_normalized : d.Yplus ⊔ d.S ≤ normalizer (YC d L : Set G)
  component_normalized : d.S ≤ normalizer (L : Set G)
  component_direction : ResidualDirection d.Yplus d.S (YL d L)
  centralizer_direction : ResidualDirection d.Yplus d.S (YC d L)
  directions : YL d L ≠ YC d L ∧ ∀ N : Subgroup G,
    ResidualDirection d.Yplus d.S N ↔ N = YL d L ∨ N = YC d L
  not_second_choice : ¬ CaseTwo d.M d.Y d.S d.V₁ d.Yplus
  first_choice : d.Yplus = d.Y
  generation : d.Y = YL d L ⊔ YC d L
  factors : ResidualPlaneFactors d L
  exchange : ∀ t ∈ (d.T : Subgroup G), t ∉ d.S → (YL d L).conjBy t = YC d L
  coordinates : ∃ i j : OrthogonalPlaneIndex, i ≠ j ∧
    movingPlane d L = d.action.plane j ∧ ⁅d.V, YC d L⁆ = d.action.plane i ∧
    ⁅movingPlane d L, YL d L⁆ = movingPlane d L ∧
    movingPlane d L ⊔ d.action.plane i = d.V ∧
    Disjoint (movingPlane d L) (d.action.plane i)
  plane_card : Nat.card (movingPlane d L) = 4
  plane_le : movingPlane d L ≤ d.S
  plane_normalized : d.S ≤ normalizer (movingPlane d L : Set G)
  plane_centralized : YC d L ≤ centralizer (movingPlane d L : Set G)
  plane_fixed : movingPlane d L ⊓ centralizer (YL d L : Set G) = ⊥

/-- Assemble the source residual reductions with no invariance or first-choice
premise. The actual parabolic supplies the moved direction, the literal
section-centralizer supplies the fixed direction, and the second-choice
normalizer contradiction forces the first-choice coordinate identification. -/
theorem residual_geometry_of_source (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥) :
    ResidualGeometry d c.L := by
  obtain ⟨P, g, hP, hM⟩ := h.parabolic
  obtain ⟨hL, hC, hSL⟩ :=
    ResidualInvariance.residuals_and_component_normalized_of_parabolic
      d hI c e P hP g hM h.normalizes_component h.quotient_card h.shadow
      h.component_three_part h.centralizer_three_part
      (h.core_le.trans (h.radical.le.trans inf_le_right)) hne
  obtain ⟨hdL, hdC⟩ := component_residual_directions d c.L h.normalizes_component
    (le_sup_right.trans hL) (le_sup_right.trans hC)
    h.component_three_part h.centralizer_three_part
  have hncase := not_caseTwo_of_residual_directions d c h.image h.quotient_card
    h.shadow hdL hdC h.generation hne hE h.core_le h.radical
  have hY := d.choice.resolve_right hncase
  have hf := residualPlaneFactors_of_first_choice d c.L hY h.image
    h.quotient_card h.shadow hdL hdC h.generation
  obtain ⟨hc, hUS, hn, hcen, hfix⟩ := movingPlane_geometry d c.L h.image hf
  exact {
    component_residual_normalized := hL
    centralizer_residual_normalized := hC
    component_normalized := hSL
    component_direction := hdL
    centralizer_direction := hdC
    directions := rankTwoShadow_residual_directions (yplus_perfect_of_choice d.choice)
      h.quotient_card (d.T.isPGroup'.to_le inf_le_left)
      (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice)
      h.shadow hdL hdC h.generation
    not_second_choice := hncase
    first_choice := hY
    generation := hY.symm.trans h.generation
    factors := hf
    exchange := residual_factors_exchanged d c.L hf
    coordinates := movingPlane_coordinates d c.L h.image hf
    plane_card := hc
    plane_le := hUS
    plane_normalized := hn
    plane_centralized := hcen
    plane_fixed := hfix }

/-- In the surviving source branch the plane lies in Z([O₂(L),L]).
Its placement follows from the span and core bounds, not a choice of V₂. -/
theorem movingPlane_le_coreCenter_of_source (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥) :
    movingPlane d c.L ≤ CoreActions.coreCenter c.L := by
  have hg := residual_geometry_of_source d hI c e h hE hne
  exact movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical

/-- The derived plane also lies in the center of the full two-core, as in
the source's parabolic-line statement. -/
theorem movingPlane_le_twoCoreCenter_of_source (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥) :
    movingPlane d c.L ≤ (center (c.L.pCoreIn 2)).map (c.L.pCoreIn 2).subtype := by
  have hg := residual_geometry_of_source d hI c e h hE hne
  have hUcore : movingPlane d c.L ≤ c.L.pCoreIn 2 :=
    (movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical).trans
      ((map_subtype_le _).trans (commutatorCore_le c.L))
  obtain ⟨_, j, _, hU, _⟩ := hg.coordinates
  have hUV : movingPlane d c.L ≤ d.V := hU ▸ d.action.plane_le j
  have hVC : d.V ≤ centralizer (c.L.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (h.core_le.trans (h.radical.le.trans inf_le_right))
  intro u hu
  exact mem_map.mpr ⟨⟨u, hUcore hu⟩,
    mem_center_iff.mpr (fun q => Subtype.ext (hVC (hUV hu) q q.property)), rfl⟩

/-- The minimal component parabolic is exactly the stabilizer of the derived
plane. Its quotient is maximal, and the two-core lies in S ∩ L, so maximality
lifts. The whole perfect component cannot normalize an order-four subgroup
on which its residual acts nontrivially. This supplies the parabolic equality
used by the independent three-layer core-action calculation. -/
theorem componentParabolic_eq_planeNormalizer_of_source
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥) :
    YL d c.L ⊔ (d.S ⊓ c.L) = c.L ⊓ normalizer (movingPlane d c.L : Set G) := by
  have hg := residual_geometry_of_source d hI c e h hE hne
  let U := movingPlane d c.L
  let M := YL d c.L ⊔ (d.S ⊓ c.L)
  let N := c.L ⊓ normalizer (U : Set G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))
  have hUL : U ≤ c.L :=
    (movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical).trans
      ((map_subtype_le _).trans ((commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)))
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hML : M ≤ c.L := sup_le hYL inf_le_right
  have hMN : M ≤ N := le_inf hML
    (componentParabolic_normalizes_movingPlane d c.L h.image hg.factors)
  have hker : f.ker ≤ M.subgroupOf c.L := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    intro x hx
    exact mem_sup_right ⟨(h.core_le.trans (R_le_S d h.radical))
      (mem_map.mpr ⟨x, hx, rfl⟩), x.property⟩
  obtain ⟨P, g, hP, hM⟩ := h.parabolic
  have hmaxP : IsCoatom P := by
    rcases hP with rfl | rfl
    · exact Matrix.PSL3Two.isCoatom_pointParabolicSL
    · exact Matrix.PSL3Two.isCoatom_lineParabolicSL
  have hmax : IsCoatom (M.subgroupOf c.L) := by
    have hc : IsCoatom (P.conjBy g) :=
      ((MulAut.conj g).mapSubgroup.isCoatom_iff P).mpr hmaxP
    have hm := isCoatom_comap_of_surjective (φ := f)
      (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 c.L))) hc
    rw [← hM, comap_map_eq_self hker] at hm
    exact hm
  have hN : N.subgroupOf c.L ≠ ⊤ := by
    intro ht
    have hLN : c.L ≤ normalizer (U : Set G) := by
      intro l hl
      exact (show (⟨l, hl⟩ : c.L) ∈ N.subgroupOf c.L from ht ▸ mem_top _).2
    let _ : (U.subgroupOf c.L).Normal := normal_subgroupOf_of_le_normalizer hLN
    let _ : Group.IsPerfect c.L := by
      let _ := c.component.perfect
      have hp := Group.IsPerfect.map (Stellmacher.elementaryAbelianMaxJ I).subtype
        (H := c.L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I))
      rwa [map_subgroupOf_eq_of_le c.le_thompson] at hp
    have hcard : Nat.card (U.subgroupOf c.L) ≤ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv]
      exact hg.plane_card.le
    have hc := le_centralizer_of_isPerfect_of_card_le_four
      (⊤ : Subgroup c.L) (U.subgroupOf c.L) hcard
    have hcen : YL d c.L ≤ centralizer (U : Set G) := by
      intro l hl u hu
      exact congrArg Subtype.val
        (hc (mem_top (⟨l, hYL hl⟩ : c.L)) ⟨u, hUL hu⟩ hu)
    have hcomm : ⁅U, YL d c.L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcen)
    obtain ⟨_, _, _, _, _, hm, _⟩ := hg.coordinates
    have hbot : U = ⊥ := hm.symm.trans hcomm
    have hcU : Nat.card U = 4 := hg.plane_card
    rw [hbot] at hcU
    norm_num at hcU
  have he := congrArg (Subgroup.map c.L.subtype)
    ((hmax.le_iff_eq hN).mp (comap_mono hMN)).symm
  simpa only [map_subgroupOf_eq_of_le hML,
    map_subgroupOf_eq_of_le (show N ≤ c.L from inf_le_left)] using he

/-- Transport the derived projective line to the actual natural layer with
the same marking e as the component parabolic. Both first/second-case Q and
third-case Z(Q) are allowed; line placement and dimension are conclusions. -/
theorem naturalPlaneSpace_geometry_of_source (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    {A : Subgroup G} {a : ℕ}
    (hA : A = commutatorCore c.L ∨ A = CoreActions.coreCenter c.L)
    (m : LayerModel c.L A ⊥ e (NaturalCopies (ZMod 2) a)) :
    movingPlane d c.L ≤ A ∧ Module.finrank (ZMod 2) (naturalPlaneSpace d m) = 2 ∧
      (∀ (l : c.L), (l : G) ∈ YL d c.L ⊔ (d.S ⊓ c.L) →
        ∀ v ∈ naturalPlaneSpace d m,
          NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v ∈ naturalPlaneSpace d m) ∧
      (∀ v ∈ naturalPlaneSpace d m,
        (∀ l : c.L, (l : G) ∈ YL d c.L →
          NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) v = v) → v = 0) := by
  have hg := residual_geometry_of_source d hI c e h hE hne
  exact naturalPlaneSpace_source_geometry d c hg.component_normalized h.core_le
    h.radical hA m h.image hg.factors

/-- Exclude the full fifth alternative from the earlier source data and
nontrivial action. The local Sylow may be smaller than S; its containment
of the moving plane is proved from the actual component-core identification. -/
theorem fifthCase_impossible_of_source (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (H : Subgroup G) (hLH : c.L ≤ H) (hcomp : (c.L.subgroupOf H).IsCComponent)
    (P : Sylow 2 H) (hPS : (P : Subgroup H).map H.subtype ≤ d.S)
    (R : Subgroup H)
    (eH : ((c.L.subgroupOf H) ⧸ pCore 2 (c.L.subgroupOf H)) ≃* Matrix.PSL3Two.SL)
    (hfive : FifthCase (c.L.subgroupOf H) R P eH) : False := by
  have hg := residual_geometry_of_source d hI c e h hE hne
  exact fifthCase_impossible_in_local_group d c hg.component_normalized
    h.core_le h.radical H hLH hcomp P hPS R eH h.image hg.factors hfive

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
end
