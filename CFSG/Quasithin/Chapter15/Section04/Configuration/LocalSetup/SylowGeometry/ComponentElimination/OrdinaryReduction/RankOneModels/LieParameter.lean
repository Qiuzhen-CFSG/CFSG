module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.SmallModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.SplitModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.Unitary
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.Triality
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.Ree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models

/-!
# Intersecting the full characteristic-two list with odd-prime PSL₂

The full case split retains the overlaps at p = 5 and p = 7 and excludes
every other alternative. Order comparisons handle the split, unitary,
Suzuki, binary-linear, and small-derived models. The genuine graph-field
triality and Ree models contain elementary abelian two-subgroups of order
at least eight, incompatible with the dihedral Sylow subgroups of odd PSL₂.
The theorem `lie_odd_parameter` assembles all of these proved comparisons
and supplies the exact characteristic-two premise of
`ComponentElimination.rank_one_models_of_comparisons`.

Source: Aschbacher–Smith, full 1.1.5(3), printed pp.501–503, and the
proof of 15.4.20, printed p.1164. The source list is the full LieTypeTwoModel;
no family disjointness or parameter conclusion is assumed by its definition.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure

/-- The characteristic-two case split with explicit twisted-model exclusions.
The unconditional theorem below supplies all three exclusions. -/
theorem lie_odd_parameter_of_twisted_exclusions
    {Q : Type*} [Group Q] {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp5 : 5 ≤ p)
    (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hunitary : ∀ f : ℕ, 2 ≤ f → ClassicalGroup.IsPSU Q 3 (2^f) → False)
    (htriality : ∀ f : ℕ, 1 ≤ f → Triality.Standard.IsTrialityGroupAt (2^f) Q → False)
    (hree : ∀ m : ℕ, 1 ≤ m → IsReeF4At Q m → False)
    (hlie : LieTypeTwoModel Q) : IsFermatOrMersennePrime p := by
  have h5 (he : p = 5) : IsFermatOrMersennePrime p :=
    ⟨hp, Or.inl ⟨1, by omega⟩⟩
  have h7 (he : p = 7) : IsFermatOrMersennePrime p :=
    ⟨hp, Or.inr ⟨3, by omega⟩⟩
  rcases hlie with h | h | ⟨n,hn,hmodel⟩
  · cases h with
    | linear f hf hmodel =>
      exact h5 (LieParameter.linear_two_odd_parameter hp ho hp5 hf hodd hmodel)
    | unitary f hf hmodel => exact (hunitary f hf hmodel).elim
    | suzuki m hm hmodel => exact (LieParameter.not_suzuki ho hm hodd hmodel).elim
  · cases h with
    | linear f hf hmodel =>
      by_cases hfone : f = 1
      · have htwo : ClassicalGroup.IsPSL Q 3 2 := by simpa [hfone] using hmodel
        exact h7 (LieParameter.linear_three_two_odd_parameter ho hodd htwo)
      · exact (LieParameter.not_linear_three ho (by omega) (by omega) hodd hmodel).elim
    | symplectic f hf hmodel =>
      exact (LieParameter.not_symplectic ho (by omega) hf hodd hmodel).elim
    | g2 f hf hmodel => exact (LieParameter.not_g2 ho (by omega) hf hodd hmodel).elim
    | triality f hf hmodel => exact (htriality f hf hmodel).elim
    | ree m hm hmodel => exact (hree m hm hmodel).elim
    | symplectic_derived hmodel =>
      exact (LieParameter.not_symplectic_derived hp hodd hmodel).elim
    | g2_derived hmodel => exact (LieParameter.not_g2_derived hodd hmodel).elim
    | tits hmodel => exact (LieParameter.not_tits hodd hmodel).elim
  · exact (LieParameter.not_binary_linear hn hodd hmodel).elim

/-- An odd-prime PSL₂ in the full characteristic-two list has a Fermat or
Mersenne parameter. All model comparisons are discharged, including the
genuine triality and Ree alternatives; the overlaps at five and seven remain. -/
theorem lie_odd_parameter
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp5 : 5 ≤ p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hlie : LieTypeTwoModel Q) :
    IsFermatOrMersennePrime p := by
  exact lie_odd_parameter_of_twisted_exclusions hp ho hp5 hodd
    (fun _ hf hmodel => LieParameter.not_unitary hp ho hp5 hodd hf hmodel)
    (fun _ hf hmodel => LieParameter.not_triality hp ho hp5 hodd hf hmodel)
    (fun _ hm hmodel => LieParameter.not_ree hp ho hp5 hodd hm hmodel)
    hlie

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
