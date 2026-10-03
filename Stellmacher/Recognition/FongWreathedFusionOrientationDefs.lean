module

public import Stellmacher.Recognition.FongWreathedFusionLocal

/-!
# The orientation choice in Fong's fusion calculation

Fong's base fusions depend on a compatible choice of the actual wreathed
presentation. The predicate below records that choice, without asserting it
for an arbitrary initial presentation. The remaining fusions and separation
are presentation independent.

Source: Fong (1967), p. 70, the change of notation and the base-normalizer
calculation immediately preceding equation (5).
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] (S : Sylow 2 G)

/-- The four base fusions specifying a compatible Fong orientation. -/
public structure BaseOrientation (P : Wreathed.Presentation S 2) : Prop where
  square_EX : IsConj ((F P ^ 2 : S) : G) ((E P * X P : S) : G)
  square_inv_E : IsConj (((F P ^ 2)⁻¹ : S) : G) ((E P : S) : G)
  X_square_EJ : IsConj ((X P * F P ^ 2 : S) : G) ((E P * J P : S) : G)
  X_square_EXJ : IsConj ((X P * F P ^ 2 : S) : G) ((E P * X P * J P : S) : G)

end Stellmacher.Recognition.FongWreathedIntrinsic
