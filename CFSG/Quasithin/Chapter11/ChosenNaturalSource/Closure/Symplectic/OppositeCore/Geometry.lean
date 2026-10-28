module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Lift
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Generation

/-!
# The geometric inputs to opposite-core transfer

The faithful marked action transports an actual model pair isomorphism to
the original action image. Its SL₂ two-core is trivial, so the original
pair core lies in O₂(LT). Three point-local model conjugators lift to
elements of the literal L₁ and supply generation modulo O₂(LT).

The final application below discharges those two transfer premises of
core_le_point_core_of_three_opposites. The opposite-pair choice, the three
model generators and the independent natural-quotient bound remain explicit.
They are not asserted as consequences of the preceding source geometry here.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The image isomorphism uses the faithful action on all of the original V. -/
def pairImageEquiv (m : MarkedFlag E) {y : G}
    (S : Subgroup (Sp E.input.field.Carrier))
    (hS : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      S.map (FullAction.modelHom m)) :
    actionImage (V := V) (oppositeJoin (auxiliaryW E) y) ≃* S :=
  (MulEquiv.subgroupCongr hS).trans
    (S.equivMapOfInjective (FullAction.modelHom m) (FullAction.modelHom_injective m)).symm

/-- The remaining geometric inputs, on the actual source action, feed the
existing opposite-core theorem. Its independent natural-quotient producer
still has to supply hQ. -/
theorem core_le_point_core_of_model_pairs (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (S : Subgroup (Sp E.input.field.Carrier))
    (hS : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      S.map (FullAction.modelHom m))
    (e : S ≃* Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier)
    (k : Fin 3 → Sp E.input.field.Carrier)
    (hk : ∀ i, k i ∈ PointModel.image m E.L₁)
    (hgen : (⨆ i, S.map (MulAut.conj (k i)).toMonoidHom) = ⊤)
    (hQ : corePair (auxiliaryW E) y ≤ E.G₁.pCoreIn 2) :
    L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  obtain ⟨l, hl, hL⟩ := three_model_pairs_lift E m hW hy S hS k hk hgen
  exact core_le_point_core_of_three_opposites E m hy hW
    (opposite_core_le_large_core E m hW hy ((pairImageEquiv E m S hS).trans e))
    hQ l hl hL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
