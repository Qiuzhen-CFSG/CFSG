module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace.Lift
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace.ModelConfiguration
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.LinearObstruction
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Transport
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Four
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five

/-!
# The two-central subspace in the further enlargement

The source configuration gives a faithful elementary actor group of order
eight, an embedded A₆, and its pointwise fixed Sylow subgroup. A two-central
actor from the binary model lifts to a subgroup of corank two containing
A₁. Its action has order two and centralizes an actual Sylow subgroup of Y.
The independently proved outer-action obstruction supplies the negative
Sylow assertion.

The intrinsic actor calculations for the actual binary linear groups in
dimensions four and five discharge both model premises in
`linearActionAnalysis`. The containing component and its model identification
remain supplied by the separate enlargement constructions. Hypothesis E.6.15
is used upstream to obtain the escape configuration and nonidentity
intersection; the action calculation below needs only E.6.1 once these are
supplied.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic BinaryLinear.SixSylowActors
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The actual field and projective-quotient equivalences retain the model's actors. -/
theorem twoCentralActor_of_psl_model {Y : Type*} [Group Y] [Finite Y]
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL Y n 2)
    (hmodel : HasTwoCentralActor (LinearGroup n)) : HasTwoCentralActor Y := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : Y ≃* LinearGroup n := e₀.trans ((Atlas.fieldEquivPSL n f.symm).trans
    (projectiveEquivLinear hn))
  let _ : Finite (LinearGroup n) := Finite.of_equiv Y e.toEquiv
  exact hmodel.of_equiv e

/-- Conditional assembly retaining the two intrinsic binary model calculations. -/
theorem linearActionAnalysis_of_modelActors [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hfour : HasTwoCentralActor (LinearGroup 4))
    (hfive : HasTwoCentralActor (LinearGroup 5)) : LinearActionAnalysis M V := by
  intro U A L X g c _ Y hY hm
  have hmodel : HasTwoCentralActor Y := by
    rcases hm.model with h4 | h5
    · exact twoCentralActor_of_psl_model (by decide) h4 hfour
    · exact twoCentralActor_of_psl_model (by decide) h5 hfive
  obtain ⟨a, ha, ha1, P, hP⟩ := hmodel _ _ (c.model_configuration h hY hm)
  exact twoCentralGeometry_of_subspace hm (subspace_of_twoCentralActor c hY hm ha ha1 P hP)

/-- The corank-two two-central subspace and the negative Sylow assertion for
the supplied further enlargement. Both binary model calculations are discharged,
and every actor and Sylow subgroup is transported through the actual model
equivalence. This applies in particular to the full known-simple class in E.6.1. -/
theorem linearActionAnalysis [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V) :
    LinearActionAnalysis M V :=
  linearActionAnalysis_of_modelActors h four_hasTwoCentralActor five_hasTwoCentralActor

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
