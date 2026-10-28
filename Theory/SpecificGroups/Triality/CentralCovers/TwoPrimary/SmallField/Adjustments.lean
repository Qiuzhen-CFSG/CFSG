module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations

/-!
# Central changes of additive folded-root lifts

Multiplying each additive root section by an additive map into the literal
central kernel preserves additivity and the prescribed root marking. These
are the permissible changes when removing defects in lifted Chevalley
relations. Their existence with compatible commutators is a separate input.

Source: the central-extension calculation underlying GLS3 §6.1, used in
Aschbacher–Smith I.1.3. The six folded-root conventions are from GLS3 §2.4.
-/

public section
open Triality.Standard
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

private def centralTwist {B E A : Type*} [Group B] [Group E] [Group A]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E)
    (s : A →* E) (c : A →* f.ker) : A →* E where
  toFun x := s x * (c x).val
  map_one' := by simp
  map_mul' x y := by
    have hc := Subgroup.mem_center_iff.mp (hk (c x).property) (s y)
    change s (x*y) * (c (x*y)).val = (s x * (c x).val) * (s y * (c y).val)
    simp only [map_mul, Subgroup.coe_mul]
    calc
      s x * s y * ((c x).val * (c y).val) =
          s x * (s y * (c x).val) * (c y).val := by group
      _ = s x * ((c x).val * s y) * (c y).val := by rw [hc]
      _ = (s x * (c x).val) * (s y * (c y).val) := by group

private theorem centralTwist_project {B E A : Type*} [Group B] [Group E] [Group A]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E)
    (s : A →* E) (c : A →* f.ker) (x : A) :
    f (centralTwist f hk s c x) = f (s x) := by
  change f (s x * (c x).val) = f (s x)
  rw [map_mul, show f (c x).val = 1 from (c x).property, mul_one]

variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]

/-- Additive corrections valued in the literal central kernel. -/
structure CentralAdjustment (f : E →* BinaryCarrier n hn) where
  shortChange : Fin 3 → Multiplicative (ExtensionField (binaryParameters n hn)) →* f.ker
  longChange : Fin 3 → Multiplicative (fixedField (binaryParameters n hn)) →* f.ker

/-- Central corrections preserve both additivity and the prescribed root projections. -/
def CentralAdjustment.adjusted {f : E →* BinaryCarrier n hn}
    (A : CentralAdjustment f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections n hn f) : RootSections n hn f where
  shortRoot i := centralTwist f hk (L.shortRoot i) (A.shortChange i)
  longRoot i := centralTwist f hk (L.longRoot i) (A.longChange i)
  project_short i t := (centralTwist_project f hk _ _ _).trans (L.project_short i t)
  project_long i t := (centralTwist_project f hk _ _ _).trans (L.project_long i t)

/-- The exact short-root correction, on the original cubic parameter. -/
theorem CentralAdjustment.adjusted_short {f : E →* BinaryCarrier n hn}
    (A : CentralAdjustment f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections n hn f) (i : Fin 3) (t : ExtensionField (binaryParameters n hn)) :
    (A.adjusted hk L).shortRoot i (.ofAdd t) =
      L.shortRoot i (.ofAdd t) * (A.shortChange i (.ofAdd t)).val := by rfl

/-- The exact long-root correction, on the original fixed-field parameter. -/
theorem CentralAdjustment.adjusted_long {f : E →* BinaryCarrier n hn}
    (A : CentralAdjustment f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections n hn f) (i : Fin 3) (t : fixedField (binaryParameters n hn)) :
    (A.adjusted hk L).longRoot i (.ofAdd t) =
      L.longRoot i (.ofAdd t) * (A.longChange i (.ofAdd t)).val := by rfl



end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
