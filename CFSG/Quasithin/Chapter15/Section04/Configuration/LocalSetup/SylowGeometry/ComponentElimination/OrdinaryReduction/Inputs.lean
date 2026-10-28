module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Structure
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic

/-!+# Source inputs for the ordinary model comparison

The contrary configuration retains the actual marked X-factors and their
S₃ × S₃ action through `PlacedX`, the corrected larger Sylow subgroup in the
core normalizer, and the intrinsic normal-closure and prime-to-three-residual
identities. The two embedding alternatives below are explicit inputs from
the preceding paragraph of 15.4.20, not recognition theorems.

The binary case uses the actual automorphism group of PSL₄(2) or PSL₅(2)
as the quotient of H. The pair case uses a C-component inside H, its actual
conjugate, and its projective two-core quotient. Neither alternative assumes
ordinary component status, trivial cores, simple models, or inner actions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed pp.1163–1164; 1.1.5, printed pp.501–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction
variable {G : Type*} [Group G]

/-- Genuine contrary data before the ordinary-model reduction. -/
structure SourceContext (d : Source.Geometry G) (i j : Bool) (H K U : Subgroup G) where
  placed : EmbeddingReduction.PlacedX d i j H U
  closure : K = EmbeddingReduction.normalClosureIn d.wholeX H
  residual : K = (primeToResidual 3 H).map H.subtype
  generation : H = K ⊔ U
  omega : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G)
  four : Nat.card d.Z = 4
  local115 : ∀ z ∈ d.Z, z ≠ 1 → ∃ (P : Sylow 2 H) (M : Subgroup G),
    Chapter1.Lemma115Hypotheses H P M z

/-- The actual automorphism-group model in alternative (i). -/
def BinaryAutomorphismModel (H : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))

/-- The precise quotient models in alternative (ii); positivity and the
Fermat/Mersenne restriction are conclusions still to be proved. -/
def RankOneQuotientModel (L : Type*) [Group L] : Prop :=
  (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) ∨
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p

/-- The ordinary seed models needed by the final pair assembly. This is an
output contract, not a consequence of the quotient model by definition. -/
def OrdinaryRankOneModel (L : Type*) [Group L] : Prop :=
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 5 ≤ p ∧ ClassicalGroup.IsPSL L 2 p) ∨
    ∃ n : ℕ, Even n ∧ 2 ≤ n ∧ ClassicalGroup.IsPSL L 2 (2 ^ n)

/-- The field in the actual model excludes exponent zero. Together with
the source parity restriction, this gives the required positive even range. -/
theorem even_exponent_ge_two {L : Type*} [Group L] {n : ℕ}
    (hn : Even n) (hL : ClassicalGroup.IsPSL L 2 (2 ^ n)) : 2 ≤ n := by
  obtain ⟨F, hF, hfin, hcard, _⟩ := hL
  have hFcard : 1 < Nat.card F := Finite.one_lt_card
  by_contra h
  obtain ⟨k, hk⟩ := hn
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero] at hcard
  omega

/-- An intrinsic C-component and its specified conjugate in H. -/
structure PairEmbedding (H K U : Subgroup G) where
  seed : Subgroup H
  cComponent : seed.IsCComponent
  conjugator : H
  conjugator_mem : (conjugator : G) ∈ U
  moves : conjugator ∉ normalizer (seed : Set H)
  product : seed ⊔ seed.map (MulAut.conj conjugator).toMonoidHom = K.subgroupOf H
  model : RankOneQuotientModel seed

/-- The two source alternatives, without an ordinary-component conclusion. -/
def EmbeddingAlternatives (H K U : Subgroup G) : Prop :=
  ((K.subgroupOf H).IsCComponent ∧ BinaryAutomorphismModel H) ∨
    Nonempty (PairEmbedding H K U)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction
