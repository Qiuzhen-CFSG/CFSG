module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FieldExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedFixerSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.InvolutionFusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Complete

/-!
# Field exclusion with the actual residual models, fusion and component sieve

The marked cover supplies the graph-field and field residuals and the
centralizer-image bound. Its involutions fuse into the two original natural
orbits. The complete selected-component sieve supplies the three terminal
models. This theorem discharges all those premises of `Reduction.field_exclusion`.

The preceding source steps retain ownership of the field-coset fusion,
component index, odd core and extraspecial Sylow-three data. Genuine
universal A/C and the original local centralizer hypotheses remain explicit.

Source: Aschbacher–Smith, proof of 15.3.38, printed pp.1136–1137.
-/

public section
open Subgroup Theory.GroupTheory MulAut
open CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open FieldExclusion
open LocalCover LocalCover.SourceBorel
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Source consumer with actual marked residuals, inside fusion and the entire
three-model sieve discharged. -/
theorem Reduction.field_exclusion_of_source {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (r : Reduction d I L) (h : Setup d I L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      TheoremC CFSG.KnownSimple.IsKnownSimple X)
    (hperfect : IsPPerfect 2 G) (z : G)
    (hzmem : z ∈ d.Z) (hzne : z ≠ 1)
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)))
    (hcoset : ∀ x : G, orderOf x = 2 → x * (r.sylow.lift.dihedral.halfTurn : G)⁻¹ ∈ L →
      IsConj x (r.sylow.lift.dihedral.halfTurn : G))
    (hindex : L.relIndex (centralizer (r.coverData.cover.borel.W₁ : Set G)) = 2)
    (eO : pPrimeCore 2 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃* ElementaryNine)
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple
      (centralizer ({(r.sylow.lift.dihedral.halfTurn : G)} : Set G)))
    (P : Sylow 3 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1) : False := by
  obtain ⟨eW⟩ := graphField_intersection_residual_model h r.coverData r.sylow.lift
  obtain ⟨eF⟩ := field_intersection_residual_model h r.coverData r.sylow.lift
  exact r.field_exclusion hA hC hperfect z
    (graphField_residual_centralizerImage_not_four h r.coverData r.sylow.lift) hz
    (r.involution_fusion h z hzmem hzne) hcoset hindex eW eO eF hH P hc he
    (fun K s => s.fieldComponentQuotient hA hC)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
