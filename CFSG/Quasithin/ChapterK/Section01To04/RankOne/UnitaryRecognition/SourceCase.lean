module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary

/-!+# Recognition applied to the full K.3.3 calculation

The earlier group-only central-quotient output now supplies the actual natural
SU₃ model used by the independent ratio proof. Thus both ratios, the binary
degree, the omega subgroup's rank and fixed dimension, and uniqueness of the
threshold subgroup hold without an additional module-identification premise.
The whole special group is retained, including its center in odd exponent.

The covering-group input is still owned by the earlier classical lifting
argument; final assembly of the rank-one families remains in RankOne.
Source: Aschbacher--Smith K.3.3, printed p.456, under printed p.451 hypotheses.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
open BenderSuzuki.MatrixGroups Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Classical
open scoped ENNReal

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  (J : HermitianForm 3 F) {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Apply the recognized column action to the literal source omega subgroup.
This discharges the natural-model premise of the independent K.3.3 ratio and
uniqueness calculation, with only the earlier group-only cover still explicit. -/
theorem source_case_of_centralQuotient (h : SourceHypotheses ρ L)
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
    (hc : IsCentralQuotient L J.specialSubgroup) (T : Sylow 2 G) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧
    Module.finrank (ZMod 2) V = 6 * s ∧
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s ∧
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 ∧
    (∀ A : Subgroup G, A ≤ T →
      ((IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
        A = omegaOneAmbient ((T : Subgroup G) ⊓ L))) := by
  obtain ⟨M⟩ := source_unitaryModel_of_centralQuotient J hs hcard hconj h hc
  exact h.unitary_case M hs hcard hconj T

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
