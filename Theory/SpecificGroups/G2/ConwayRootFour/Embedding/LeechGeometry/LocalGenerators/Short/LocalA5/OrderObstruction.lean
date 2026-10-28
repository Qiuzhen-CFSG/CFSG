module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Transport
public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity

/-!
# The ambient order obstruction for diagonal identification

An action realized in any long frame cannot have order seventeen: its order
divides that of its lift, and seventeen does not divide the proved order of
the literal Leech central quotient. Only injectivity of the coordinate map
is used; no faithfulness of the whole centralizer is required.

This supplies an ambient constraint for repairing the diagonal-identification
step in Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.284.
-/

public section
open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
open OctonionLocals

/-- Orders in a realized coordinate action divide orders of actual lifts. -/
theorem action_order_dvd (L : LongFrame) (g : LeechCentralQuotient)
    (a : LinearGroup)
    (h : ∀ v, quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (a v)) :
    orderOf a ∣ orderOf g := by
  have hp (n : ℕ) (v : Six F) :
      quotientModTwoRepresentation (g ^ n) (L.coordinates v) = L.coordinates ((a ^ n) v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, LinearEquiv.mul_apply, ih, h, pow_succ', LinearEquiv.mul_apply]
  apply orderOf_dvd_of_pow_eq_one
  apply LinearEquiv.ext
  intro v
  apply L.coordinates_injective
  rw [← hp, pow_orderOf_eq_one, map_one]
  rfl

/-- A coordinate action of order seventeen has no lift in this quotient. -/
theorem no_order_seventeen (L : LongFrame) (g : LeechCentralQuotient)
    (a : LinearGroup)
    (h : ∀ v, quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (a v)) :
    orderOf a ≠ 17 := by
  intro ha
  have hd := (action_order_dvd L g a h).trans (orderOf_dvd_natCard g)
  rw [ha, leechCentralQuotient_order] at hd
  norm_num at hd

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
