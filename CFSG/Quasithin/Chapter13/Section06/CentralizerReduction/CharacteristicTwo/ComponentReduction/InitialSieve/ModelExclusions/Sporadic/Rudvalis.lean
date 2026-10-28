module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic.RudvalisReduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowCenter

/-!
# The Rudvalis exclusion from stabilizer-class preservation

The intrinsic center bound for every Sylow two-subgroup of the literal
Rudvalis model discharges the center premise of RudvalisReduction. The sole
remaining model premise is preservation of its actual degree-4060 point
stabilizers. The second theorem applies the resulting bound to the faithful
four-group from ActionData on the genuine component quotient K/O₂(K), with
trivial ambient odd core and an actual model isomorphism.

Source: Aschbacher–Smith, 1.1.5(3)(f), pp.501–503, and the sporadic branch of
13.6.6, printed p.927; GLS3 Table 5.3r. Stabilizer preservation is the
remaining explicit model premise.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
open A5Module

/-- The exact point-stabilizer premise suffices; the Sylow-center bound is intrinsic. -/
theorem ru_smallSylowFixers_of_stabilizers
    (hstable : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (f : MulAut Rudvalis.Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y) :
    SmallSylowFixers Rudvalis.Model :=
  rudvalis_smallSylowFixers_of_centers_and_stabilizers
    (by intro _ _ P; exact Rudvalis.SylowCenter.sylow_center_card_le_two P) hstable

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- Conditional exclusion for the literal two-core quotient of a genuine component. -/
theorem not_ru_quotient_of_stabilizers
    (hstable : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (f : MulAut Rudvalis.Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) :=
  not_quotient_of_smallSylowFixers (ru_smallSylowFixers_of_stabilizers hstable) K hK hodd a

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
