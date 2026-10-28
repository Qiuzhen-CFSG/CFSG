module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Assembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.InitialAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Products
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Source controls for the terminal contradictions of 15.3.1

The actual quadratic form and its constructed wreath coordinates define the
same singular subgroups. The comparison checks the sixteen original vectors,
then uses the existing form equality without changing either action. Source
15.3.46(2) also controls the original definite plane: a singular subgroup is
disjoint from that plane, whereas the plane itself has order four. Thus the
separate 15.3.45(2) control in the endgame record is derived from the full
15.3.46(2) conclusion. The earlier-fusion constructor still uses the genuine
upstream inputs of 15.3.46, including the preceding definite-plane bounds.

The existing two-three solvability theorem applies to the prime support
already produced by the terminal configuration. Escape of X_E follows from
the selected escaping line, the initial Sylow promotion and 15.3.66's product;
it does not need the later I₀ field restriction or quotient recognition.

The terminal consumer constructs all four endgame controls and applies the
built two-branch contradiction. Actual local construction, the compatible
coordinate witness produced by the earlier source theorem, and the full
F.6/B.5 classification witnesses remain with the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.45–46,
15.3.66–68 and the final proof of 15.3.1, printed pp.1140–1141, 1152–1155;
PDF p.1172 for the terminal contradiction.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls

open Subgroup AbelianAmalgam TerminalRecognition TerminalRecognition.ExceptionalAction
open scoped IsMulCommutative

private theorem coordinate_singular_iff : ∀ v : OrthogonalVector,
    FusionCore.orthogonalCoordinateValue v = 0 ↔
      ∀ i j : OrthogonalPlaneIndex, v i = 1 ↔ v j = 1 := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G] {G₀ M V P : Subgroup G}

omit [Finite G] in
/-- The definite-plane control follows from the already available full
15.3.46(2) implication and the actual supported plane of order four. -/
theorem definite_normalizer_of_singular_control
    (d : NaturalOrthogonalAction M V)
    (h46 : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      MarkedPlane.IsSingularIn M V U d) : normalizer (d.plane 1 : Set G) ≤ M := by
  by_contra hn
  have hs := h46 (d.plane 1) (d.plane_le 1) hn
  have hbot : d.plane 1 = ⊥ :=
    disjoint_self.mp (MarkedPlane.singular_disjoint_plane hs 1)
  have hc := d.card_plane 1
  rw [hbot, Subgroup.card_bot] at hc
  norm_num at hc

omit [Finite G] in
/-- Singularity for the original quadratic form is singularity in the
constructed coordinates, with the same ambient subgroup. -/
theorem singularIn_of_totallySingular [IsElementaryAbelian 2 V]
    {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P) {U : Subgroup G}
    (hU : FusionCore.IsTotallySingular q.form U) :
    MarkedPlane.IsSingularIn M V U k.action := by
  refine ⟨hU.1, ?_⟩
  intro v hv
  exact (coordinate_singular_iff (k.action.coordinates v)).mp
    ((k.form_eq v).symm.trans (hU.2 v hv))

/-- Assemble the endgame controls from source singularity, prime support
and residual escape, deriving the separate definite-plane normalizer bound. -/
theorem controls_of_quadratic_source [IsElementaryAbelian 2 V]
    {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P)
    {a : Intersection.SourceInput (V.subgroupOf G₀)}
    (g : EarlierGeometry k.action a)
    (h46 : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      FusionCore.IsTotallySingular q.form U)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hescape : ¬ lineX g.E ≤ M) : TerminalSourceEndgame.EarlierControls g where
  normalizer_escape_singular := fun U hUV hn =>
    singularIn_of_totallySingular k (h46 U hUV hn)
  definite_normalizer := definite_normalizer_of_singular_control k.action
    (fun U hUV hn => singularIn_of_totallySingular k (h46 U hUV hn))
  solvable := Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three M hsupport
  residual_escape := hescape

/-- Construct the controls directly from the completed source-46 theorem.
The earlier-fusion inputs retain their original upstream normalizer bounds. -/
theorem controls_of_earlier_fusion_inputs [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P)
    {a : Intersection.SourceInput (V.subgroupOf G₀)}
    (g : EarlierGeometry k.action a)
    (f : FusionCore.EarlierFusionInputs T M V P)
    (hP : FusionCore.IsDefinitePlane q.form P)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hescape : ¬ lineX g.E ≤ M) : TerminalSourceEndgame.EarlierControls g :=
  controls_of_quadratic_source k g
    (FusionCore.lemma_15_3_46_of_earlier_inputs q f hP).2.1.2 hsupport hescape

/-- The terminal configuration already supplies M's prime support. -/
theorem solvable_of_terminal_configuration {T : Sylow 2 G} {Y E F : Subgroup G}
    {d : OrthogonalFourBinary.NaturalAction V M}
    (c : GoldschmidtCore.TerminalConfiguration T M Y V E F d) : Group.IsSolvable M :=
  Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three M c.support_M

/-- Residual escape needs only the initial structure and 15.3.66, before
the actual I0 recognition and the full descent theorem. -/
theorem residual_escape_of_earlier_data {T : Sylow 2 G} {Mc V₁ E : Subgroup G}
    [IsElementaryAbelian 2 (localModule T M)]
    (s : LocalStructure.EarlierData T M Mc V₁ E) : ¬ lineX E ≤ M := by
  let c := LocalStructure.initialStructure s
  have hTM := s.ordering.1.2
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTY : (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) :=
    hTM.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  obtain ⟨_, _, _, _, hgeom⟩ := Orthogonal.residualY_lineNormalizer_consequences
    s.natural Mc T E hTM s.line_le s.line_card s.line_singular s.residual_image
    s.residual_core_module s.selected s.selected_map
  exact Descent.lineX_not_le_of_escape M (residualY M Mc) T E c.line_sylow
    c.line_sylow_map hTY hYM hTM s.escape hgeom

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u

/-- Actual consumer of the coordinate/control bridge. The model is the
already constructed comparison from the original quadratic source action;
all its subgroup and vector markings are retained. -/
theorem terminal_contradiction_from_quadratic_controls
    {G : Type u} [Group G] [Finite G] {G₀ M V P : Subgroup G}
    [IsElementaryAbelian 2 V] {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P)
    {a : Intersection.SourceInput (V.subgroupOf G₀)} (g : EarlierGeometry k.action a)
    (h46 : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      FusionCore.IsTotallySingular q.form U)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hescape : ¬ lineX g.E ≤ M)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) : False :=
  TerminalSourceEndgame.terminal_contradiction_of_ambient_span g
    (controls_of_quadratic_source k g h46 hsupport hescape)
    hG₀ classificationF classificationB hZE hspan

/-- The terminal contradiction with the singular-normalizer control itself
derived from the enumerated earlier fusion inputs. -/
theorem terminal_contradiction_from_earlier_fusion
    {G : Type u} [Group G] [Finite G] {G₀ M V P : Subgroup G}
    [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P)
    {a : Intersection.SourceInput (V.subgroupOf G₀)} (g : EarlierGeometry k.action a)
    (f : FusionCore.EarlierFusionInputs T M V P)
    (hP : FusionCore.IsDefinitePlane q.form P)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hescape : ¬ lineX g.E ≤ M)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) : False :=
  TerminalSourceEndgame.terminal_contradiction_of_ambient_span g
    (controls_of_earlier_fusion_inputs k g f hP hsupport hescape)
    hG₀ classificationF classificationB hZE hspan

end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls
