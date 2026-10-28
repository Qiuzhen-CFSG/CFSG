module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Maximizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension

/-!
# The end-radical offender estimate

The relative squared-offender maximizer promotes a nontrivial offender inside
the radical to the entire radical, using minimal normality in the parabolic.
The geometric radical has rank four. Thus a common-fixed-space codimension of
at least nine contradicts its squared-offender inequality.

The geometric identification and the root-group codimension certificates
discharge both premises of the reduction, proving `radical_estimate` under
the original faithful irreducible binary representation hypotheses. The proof
uses the actual relative two-core and its literal inclusion into SL₅, without
a half-dimension bound or a field-of-definition comparison.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Lemma 2.1 and
Proposition 4.7, step 1, manuscript pp.5 and 25; Aschbacher–Smith K.3.2,
printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The fixed-space comparison uses the literal inclusion of the parabolic
and the marked ambient root group. -/
theorem radical_fixedCodim_eq_rootGroup (hgeometry : RadicalGeometry) (e : Fin 2) :
    fixedCodim (σ.comp (parabolic e).subtype) (radical e) =
      fixedCodim σ (radicalRootGroup e) := by
  unfold fixedCodim
  rw [fixedSpace_comp_map, (hgeometry e).2.2.2]

/-- Conditional source application of radical maximization. The two explicit
premises have independent geometric and representation-theoretic producers;
neither premise is discharged by this assembly theorem. -/
theorem radical_estimate_of_geometry_of_root_codimension
    [FiniteDimensional (ZMod 2) V]
    (hgeometry : RadicalGeometry) (hroot : RootCodimensionEstimate σ) :
    RadicalEstimate σ := by
  intro e J v hv hhighest hsupport C hCU hC _hcubic
  obtain ⟨hU, hrank, hminimal, _⟩ := hgeometry e
  have hlarge := hroot e J v hv hhighest hsupport
  by_contra hnot
  have hsmall := RadicalMaximizer.fixedCodim_le_twice_rank_of_minimal_normal
    (σ.comp (parabolic e).subtype) (radical e) hU hminimal hCU hC
    (le_of_not_gt hnot)
  rw [radical_fixedCodim_eq_rootGroup σ hgeometry e, hrank] at hsmall
  omega

/-- The radical branch of the end-node sieve: multiple support away from the
selected end excludes every nontrivial elementary cubic offender in its actual
parabolic two-core. This discharges the radical premise of
`end_node_sieve_of_estimates`. -/
theorem radical_estimate [FiniteDimensional (ZMod 2) V]
    (hfaithful : Function.Injective σ) (hirreducible : Representation.IsIrreducible σ) :
    RadicalEstimate σ :=
  radical_estimate_of_geometry_of_root_codimension σ radical_geometry
    (root_codimension_estimate σ hfaithful hirreducible)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
