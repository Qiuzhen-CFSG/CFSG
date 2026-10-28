module

public import Theory.SpecificGroups.Triality.BinaryWeakRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ComponentRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SevenPlane

/-!
# The triality endpoint with the weaker sufficient rank bound

The actual root-word calculation supplies automorphism two-rank at most ten
from genuine coverage. The seven-plane degree bound gives dimension at least
24, contradicting the original component bound at most 22. Simplicity and
perfectness needed by coverage are inherited from that original component.
Only the actual seven-plane construction and automorphism coverage remain
explicit; no matrix identity, degree estimate or rank premise is assumed.
Source: Aschbacher–Smith G.9.3, printed p.356.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Triality.Standard
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {rho : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The actual G.9 endpoint, with its two independently owned model inputs. -/
theorem not_triality_two_of_weak_rank_and_coverage
    (d : QuaternionSevenPlane.Data (BinaryCarrier 1 Nat.zero_lt_one))
    (h : ComponentHypothesis K rho A L L m)
    (model : IsTrialityGroupAt 2 L)
    (hcoverage : IsSimpleGroup (BinaryCarrier 1 Nat.zero_lt_one) →
      Group.IsPerfect (BinaryCarrier 1 Nat.zero_lt_one) →
      ∀ a : MulAut (BinaryCarrier 1 Nat.zero_lt_one),
        ∃ g : BinaryCarrier 1 Nat.zero_lt_one,
        ∃ f : OuterOdd.CoefficientAut (binaryParameters 1 Nat.zero_lt_one),
          a = MulAut.conj g * OuterOdd.coefficientAction
            (binaryParameters 1 Nat.zero_lt_one) f) : False := by
  obtain ⟨e⟩ := (isTrialityGroupAt_two_iff L).mp model
  apply not_triality_two_of_sevenPlane_data d h model
  exact actor_rank_le_of_inherited_model_estimate h e
    (fun hs hp => BinaryWeakRank.endpoint_automorphism_rank_le_ten (hcoverage hs hp))

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
