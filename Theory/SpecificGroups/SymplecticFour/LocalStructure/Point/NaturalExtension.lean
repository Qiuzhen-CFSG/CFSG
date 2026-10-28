module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# The point-local group as an explicit natural extension

The proved point-local matrix calculation supplies the shared `NaturalExtension`
interface with no additional premises. Its projection and module isomorphism
are exactly `pointQuotient` and `pointCentralQuotientEquiv`. The conjugate in the
interface retains the same subgroup embedding as `pointRadicalConjugate`, so the
intertwining clause follows from the literal natural matrix action calculation.

Keeping this adapter separate lets the coordinate and generation proofs remain
independent of the recognition results. The latter can now identify the radical
with the two-core and derive perfectness and the block clauses.

Source: the point-local calculation for Aschbacher--Smith F.1.12(I)(2),
`refs/quasithin.pdf`, printed pp.262--264 (1 March 2004 manuscript).
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual point-local extension, constructed from its checked matrix maps. -/
def pointNaturalExtension {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    NaturalExtension (F := F) (pointRadical (F := F)) where
  elementary := pointRadical_elementaryAbelian
  projection := pointQuotient
  surjective := pointQuotient_surjective
  kernel := pointQuotient_ker
  commutator_eq := pointRadical_commutator_eq hcard hn
  moduleIso := pointCentralQuotientEquiv
  intertwining l q := congrArg Multiplicative.toAdd
    (pointCentralQuotientEquiv_conjugate l q)

/-- The recognition interface uses the original middle-block projection. -/
@[simp] theorem pointNaturalExtension_projection {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (pointNaturalExtension hcard hn).projection = pointQuotient := by rfl

/-- The recognition interface uses the proved central-quotient equivalence. -/
@[simp] theorem pointNaturalExtension_moduleIso {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (pointNaturalExtension hcard hn).moduleIso = pointCentralQuotientEquiv := by rfl

end Theory.SpecificGroups.SymplecticFour
