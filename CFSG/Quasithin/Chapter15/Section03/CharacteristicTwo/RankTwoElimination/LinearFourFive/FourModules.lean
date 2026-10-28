module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Splitting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.Displacement

/-!
# The four-dimensional module step in 15.3.24

The earlier residual image and span give the nontrivial action of Y₊ on Z.
The actual E₉ and S₃ × S₃ quotients give inner Sylow action and the
dimension-two parabolic marking. The Thompson relation then supplies the
FF hypotheses for the actual commutator module. Universal B.5.1, with the
orthogonal central cover excluded, leaves the two natural alternatives.
The repeated-natural residual and fixed-space calculations contradict the
plane-normalizer bound in the second choice of Hypothesis 15.3.10.

`naturalDual_plane_split` assembles these steps and the checked extension
splitting. Its plane uses the same model marking as the surviving natural
plus dual module. The larger central submodule C_{W_L}(L) is retained.
The exact earlier local conclusions and the universal B.5.1/B.4.2 and
I.1.6(6) inputs remain explicit; no local alternative, preparation output,
splitting, residual calculation or terminal containment is assumed. The
subsequent natural-plus-dual contradiction belongs to the parent 15.3.24
assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed pp.1129–1130 (PDF pp.1146–1147).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

universe u
variable {G : Type u} [Group G] [Finite G] (d : LocalData G)
  {I : Subgroup G} (c : ComponentWitness d I)

private theorem seed_commutator_ne_bot
    (h7image : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V) : ⁅d.Z, d.Yplus⁆ ≠ ⊥ := by
  have hnoncentral : ¬ d.Yplus ≤ centralizer (d.V : Set G) := by
    rcases d.choice with hfirst | hsecond
    · intro hc
      change d.Yplus = d.Y at hfirst
      have hcomm := d.action.commutator_eq_of_residual_image d.Y
        (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h7image
      rw [← hfirst] at hcomm
      exact OutsideStructure.LocalBranches.v_ne_bot d (hcomm.symm.trans
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
    · exact OutsideStructure.LocalBranches.second_choice_noncentral d hsecond h7image
  intro hz
  have hVC : d.V ≤ centralizer (d.Yplus : Set G) := by
    rw [← h7span]
    exact conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hz)
      ((le_sup_left.trans (OutsideStructure.LocalBranches.ys_normalizes_yplus d)).trans
        (normalizer_le_normalizer_centralizer d.Yplus))
  exact hnoncentral (le_centralizer_iff.mp hVC)

/-- The four-dimensional reduction through the repeated-natural exclusion
in 15.3.24. The local premises are the actual earlier source conclusions:
`earlier` contains the Sylow, theta, cubic and Frattini quotient clauses;
`hW`, `hred`, `hLRcore` and `hJ` are the span and Thompson conclusions
used in 15.3.16; `hMc`, `hinter`, `h7image`, `h7span` and `h7` retain the
centralizer, image, span and complete 15.3.7 alternatives. The classification and cohomology inputs are universal
statements about genuine representations, independent of this configuration.

Both module alternatives are constructed. The plane marking is reconstructed
for the surviving module's own model, and the displayed B.2.14 identity is
proved using the checked splitting of the whole component span. -/
theorem naturalDual_plane_split
    (classification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2) (earlier : Preparation.Earlier d c)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple I)
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (hW : d.componentSpan c.L ≤ c.L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R))
    (hLRcore : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hinter : d.M ⊓ d.Mc =
      (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G))
    (h7image : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    ∃ h : NaturalDual d c.L, Nonempty (PlaneParabolic d c.L h.model) ∧
      spanCommutator d c.L ⊔ d.Z =
        spanCommutator d c.L ⊔ centralSupplement d c.L := by
  obtain ⟨_, _, inner, p, _⟩ :=
    Preparation.source_preparation hI hf hrank earlier model
  have alternatives := Alternatives.moduleAlternatives d c classification cohomology
    hI earlier hSQTK model inner p.marking hW hred hLRcore hJ hR hC
    (seed_commutator_ne_bot d h7image h7span)
  let _ := hred.elementary
  let _ : IsElementaryAbelian 2 (d.componentSpan c.L) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hW).toMonoidHom
      (subgroupOfEquivOfLe hW).surjective
  have split := alternatives_centralSupplement_split earlier.core_le_R hR alternatives
  rcases alternatives with repeated | dual
  · obtain ⟨r, _, _, ⟨h⟩⟩ := repeated
    obtain ⟨p⟩ := Preparation.nonempty_planeParabolic earlier h.model
    exact (Repeated.repeated_natural_excluded earlier hR hMc hinter h p h7).elim
  · obtain ⟨h⟩ := dual
    exact ⟨h, Preparation.nonempty_planeParabolic earlier h.model, split⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules

end
