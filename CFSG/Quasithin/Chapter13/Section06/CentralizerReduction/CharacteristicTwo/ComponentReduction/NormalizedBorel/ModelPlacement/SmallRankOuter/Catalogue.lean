module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.ReeF4.CubicRank
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The full small-three-rank binary catalogue

The binary symplectic and G₂ derived subgroups and the Tits subgroup of
Ree-F₄ rule out those families. The signed-three cubic witnesses force
the opposite parameter parities. The four exponent-one constructors
contradict the source's large-field hypothesis.

The elementary nine in the genuine triality carrier is an explicit input
to this catalogue interface. `SmallRankOuter.lean` discharges it using
`Theory/SpecificGroups/Triality/ElementaryNine.lean`. The complete catalogue
is inspected here; no reduced list or outer-group property is assumed.

Source: Aschbacher–Smith, proof of 13.6.6(ii), printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.SmallRankOuter
open Subgroup Theory.GroupTheory InitialSieve
open Theory.SpecificGroups.Classical
open scoped MatrixGroups

/-- Inspection of every binary constructor at three-rank at most one,
given the actual triality elementary nine. -/
theorem small_three_rank_models_of_triality_nine
    (htriality : ∀ (f : ℕ) (hf : 1 < f),
      ∃ E : Subgroup (Triality.Standard.BinaryCarrier f (by omega)),
        IsElementaryAbelian 3 E ∧ Nat.card E = 9)
    {D : Type*} [Group D] [Finite D] {m : ℕ}
    (hm : 1 < m) (hmodel : BinaryModelAt D m) (hr : primeRank 3 D ≤ 1) :
    ClassicalGroup.IsPSL D 2 (2 ^ m) ∨
      (ClassicalGroup.IsPSL D 3 (2 ^ m) ∧ Odd m) ∨
      (ClassicalGroup.IsPSU D 3 (2 ^ m) ∧ Even m) ∨
      ∃ n : ℕ, 1 ≤ n ∧ m = 2 * n + 1 ∧
        Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n) := by
  cases hmodel with
  | linear_two m _ iso => exact Or.inl iso
  | unitary_three m _ iso =>
    refine Or.inr (Or.inr (Or.inl ⟨iso, ?_⟩))
    obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := iso
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_injective e.symm e.symm.injective
    have hrF : primeRank 3 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
      rwa [← primeRank_equiv 3 e]
    exact BinarySmallThreeRankOuter.unitary_degree_even J (by omega) hc hconj hrF
  | suzuki n hn iso => exact Or.inr (Or.inr (Or.inr ⟨n, hn, rfl, iso⟩))
  | linear_three m _ iso =>
    refine Or.inr (Or.inl ⟨iso, ?_⟩)
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := iso
    apply BinarySmallThreeRankOuter.linear_degree_odd hc
    rwa [← primeRank_equiv 3 e]
  | symplectic m _ iso =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    let e' := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    have hrF : primeRank 3 (Matrix.symplecticGroup (Fin 2) F) ≤ 1 := by
      rwa [← primeRank_equiv 3 e']
    have hl := BinaryDerivedCubicRank.symplectic (F := F)
    have hi := Theory.GroupTheory.primeRank_le_of_injective 3
      (commutator (Matrix.symplecticGroup (Fin 2) F)).subtype Subtype.val_injective
    omega
  | g2 m _ iso =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    have hrF : primeRank 3 (Atlas.G2.Model F) ≤ 1 := by
      rwa [← primeRank_equiv 3 e]
    have hl := BinaryDerivedCubicRank.g2 (F := F)
    have hi := Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype
      Subtype.val_injective
    omega
  | triality m _ iso =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff D m (by omega)).mp iso
    obtain ⟨E, hE, hcard⟩ := htriality m hm
    let := hE
    have hrF : primeRank 3 (Triality.Standard.BinaryCarrier m (by omega)) ≤ 1 := by
      rwa [← primeRank_equiv 3 e]
    have h := IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrF E
    omega
  | ree n _ iso =>
    obtain ⟨d, ⟨e⟩⟩ := iso
    have hl := ReeF4.CubicRank.fixedGroup d
    rw [← primeRank_equiv 3 e] at hl
    omega
  | symplectic_derived _ => omega
  | g2_derived _ => omega
  | tits _ => omega
  | binary_linear _ _ _ => omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.SmallRankOuter
