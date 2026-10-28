module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Raw
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Primary
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Weyl
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Descent
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Normalizer
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order

/-!
# Three-primary assembly from rational nonsplit triality words

The scalar factors have orders q³+1 and q+1. A square-root shear makes the
central reflection diagonal. Their Sylow three-subgroups therefore have a
pair of generators whose lifted alternating pairing vanishes. The cycle and
inverter descend through the same injective map, and the actual torus index
then supplies the full three-local geometry.

The rational descent and algebraic Weyl calculations are supplied by `Descent`
and `Weyl`. The resulting `torus` has order (q³+1)(q+1), including 27 at q=2.
Its configuration has no remaining construction premises; when 3 divides q+1,
`geometry` supplies the nonsplit branch of the three-primary cover argument.
Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3, with torus conventions
from §§2.1–2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
open Subgroup PerfectCentralCovering.OddSylow

namespace RationalRealization
variable {n : ℕ} {hn : 0 < n} (d : RationalRealization n hn)

/-- Undo the common conjugation to compare every descended word literally. -/
def comparison : Standard.BinaryCarrier n hn →* Ambient :=
  (MulAut.conj d.conjugator).toMonoidHom.comp d.embedding

theorem comparison_injective : Function.Injective d.comparison :=
  (MulAut.conj d.conjugator).injective.comp d.embedding_injective

@[simp] theorem comparison_torus (a : Coordinates n) :
    d.comparison (d.torus a) = rawTorus n a := by
  change d.conjugator * d.embedding (d.torus a) * d.conjugator⁻¹ = _
  rw [d.torus_eq]
  group

@[simp] theorem comparison_reflection : d.comparison d.reflection = reflectionWord := by
  change d.conjugator * d.embedding d.reflection * d.conjugator⁻¹ = _
  rw [d.reflection_eq]
  group

@[simp] theorem comparison_cycle : d.comparison d.cycle = cycleWord := by
  change d.conjugator * d.embedding d.cycle * d.conjugator⁻¹ = _
  rw [d.cycle_eq]
  group

@[simp] theorem comparison_inverter : d.comparison d.inverter = inverterWord := by
  change d.conjugator * d.embedding d.inverter * d.conjugator⁻¹ = _
  rw [d.inverter_eq]
  group

theorem torus_injective : Function.Injective d.torus := by
  intro a b h
  apply rawTorus_injective n
  simpa using congrArg d.comparison h

/-- This is the actual carrier subgroup obtained from rational descent. -/
def subgroup : Subgroup (Standard.BinaryCarrier n hn) := d.torus.range

theorem card_subgroup : Nat.card d.subgroup = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) := by
  rw [subgroup, ← Nat.card_congr (MonoidHom.ofInjective d.torus_injective).toEquiv]
  exact card_coordinates n hn

theorem mem_range_iff (x : Standard.BinaryCarrier n hn) :
    x ∈ d.torus.range ↔ d.comparison x ∈ (rawTorus n).range := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (d.comparison_torus a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, d.comparison_injective ?_⟩
    exact (d.comparison_torus a).trans ha

/-- Simultaneous descent reflects the algebraic normalizer equations. -/
theorem configuration (w : WeylLaws n) : Nonempty (Configuration d.subgroup) := by
  let j : Coordinates n →* Standard.BinaryCarrier n hn :=
    d.torus.comp (diagonalize n).toMonoidHom
  have he (a : Coordinates n) : d.comparison (j a) = rawTorus n (diagonalize n a) :=
    d.comparison_torus _
  have hrange : j.range = d.torus.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨diagonalize n a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(diagonalize n).symm a, by simp [j]⟩
  have hs : ∀ a b, d.reflection * j (a,b) * d.reflection⁻¹ = j (a,b⁻¹) := by
    intro a b
    apply d.comparison_injective
    simp only [map_mul, map_inv, d.comparison_reflection, he]
    rw [w.reflection_action, reflection_diagonalize n hn]
  have hc : orderOf d.cycle = 3 := by
    rw [← orderOf_injective d.comparison d.comparison_injective, d.comparison_cycle]
    exact w.cycle_order
  have hout : d.cycle ∉ j.range := by
    rw [hrange, d.mem_range_iff, d.comparison_cycle]
    exact w.cycle_outside
  have hnorm : d.cycle ∈ normalizer (j.range : Set (Standard.BinaryCarrier n hn)) := by
    rw [hrange, mem_normalizer_iff]
    intro x
    rw [d.mem_range_iff, d.mem_range_iff]
    simp only [map_mul, map_inv, d.comparison_cycle]
    exact mem_normalizer_iff.mp w.cycle_normalizes (d.comparison x)
  have hinv : ∀ a, d.inverter * j a * d.inverter⁻¹ = (j a)⁻¹ := by
    intro a
    apply d.comparison_injective
    simp only [map_mul, map_inv, d.comparison_inverter, he]
    exact w.inverter_action _
  have hfix : Commute d.inverter d.cycle := by
    apply d.comparison_injective
    simp only [map_mul, d.comparison_inverter, d.comparison_cycle]
    exact (Commute.refl coxeter).pow_pow 3 2
  rw [show d.subgroup = j.range from hrange.symm]
  exact configuration_of_diagonal_normalizer j d.reflection d.cycle d.inverter
    hs hc hout hnorm hinv hfix

include d

/-- The precise nonsplit witness requested by the source assembly, conditional
only on the two independent concrete construction results. -/
theorem exists_configuration (w : WeylLaws n) :
    ∃ A : Subgroup (Standard.BinaryCarrier n hn),
      Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧ Nonempty (Configuration A) :=
  ⟨d.subgroup, d.card_subgroup, d.configuration w⟩

/-- The index calculation supplies the missing ambient Sylow factor of three. -/
theorem geometry (w : WeylLaws n) (hd : 3 ∣ 2 ^ n + 1) :
    Geometry 3 (Standard.BinaryCarrier n hn) := by
  obtain ⟨cfg⟩ := d.configuration w
  exact cfg.geometry (nine_not_dvd_nonsplit_torus_index n hn d.subgroup d.card_subgroup hd)

end RationalRealization

/-- A simultaneous rational realization of the torus and the three Weyl words,
constructed by the Spin Lang argument and the genuine carrier comparison. -/
def realization (n : ℕ) (hn : 0 < n) : RationalRealization n hn :=
  Classical.choice (rationalRealization_nonempty n hn)

/-- The norm-one coroot parametrization in the original graph-field carrier. -/
def torusHom (n : ℕ) (hn : 0 < n) : Coordinates n →* Standard.BinaryCarrier n hn :=
  (realization n hn).torus

theorem torusHom_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (torusHom n hn) := (realization n hn).torus_injective

/-- The rational nonsplit torus, retaining its unequal cyclic factors. -/
def torus (n : ℕ) (hn : 0 < n) : Subgroup (Standard.BinaryCarrier n hn) :=
  (torusHom n hn).range

/-- The marked coordinates identify with the whole concrete torus. -/
def torusEquiv (n : ℕ) (hn : 0 < n) : Coordinates n ≃* torus n hn :=
  MonoidHom.ofInjective (torusHom_injective n hn)

theorem card_torus (n : ℕ) (hn : 0 < n) :
    Nat.card (torus n hn) = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) :=
  (realization n hn).card_subgroup

/-- The smallest parameter gives the full torus of order 27. -/
theorem card_torus_one : Nat.card (torus 1 (by decide)) = 27 := by
  simpa using card_torus 1 (by decide)

/-- Literal comparison with the algebraic coroot product through one conjugator. -/
theorem torusHom_embedding (n : ℕ) (hn : 0 < n) (a : Coordinates n) :
    (realization n hn).embedding (torusHom n hn a) =
      (realization n hn).conjugator⁻¹ * rawTorus n a * (realization n hn).conjugator :=
  (realization n hn).torus_eq a

/-- In the original coordinates the central reflection uses the norm q²−q+1. -/
theorem reflection_torusHom (n : ℕ) (hn : 0 < n) (a : Coordinates n) :
    (realization n hn).reflection * torusHom n hn a * (realization n hn).reflection⁻¹ =
      torusHom n hn (reflection n a) := by
  apply (realization n hn).comparison_injective
  simpa only [map_mul, map_inv, torusHom, RationalRealization.comparison_reflection,
    RationalRealization.comparison_torus] using reflectionWord_rawTorus n a

/-- After the square-root shear the reflection fixes the first cyclic factor
and inverts the second, for use in odd-primary torus arguments. -/
theorem reflection_diagonal_torusHom (n : ℕ) (hn : 0 < n) (a : Large n) (b : Small n) :
    (realization n hn).reflection * torusHom n hn (diagonalize n (a, b)) *
        (realization n hn).reflection⁻¹ = torusHom n hn (diagonalize n (a, b⁻¹)) := by
  rw [reflection_torusHom, reflection_diagonalize n hn]

theorem cycle_order (n : ℕ) (hn : 0 < n) : orderOf (realization n hn).cycle = 3 := by
  rw [← orderOf_injective (realization n hn).comparison
    (realization n hn).comparison_injective, RationalRealization.comparison_cycle]
  exact cycleWord_order

theorem cycle_outside (n : ℕ) (hn : 0 < n) :
    (realization n hn).cycle ∉ torus n hn := by
  change (realization n hn).cycle ∉ (realization n hn).torus.range
  rw [(realization n hn).mem_range_iff, RationalRealization.comparison_cycle]
  exact cycleWord_outside_rawTorus n

theorem cycle_normalizes (n : ℕ) (hn : 0 < n) :
    (realization n hn).cycle ∈ normalizer (torus n hn : Set (Standard.BinaryCarrier n hn)) := by
  rw [mem_normalizer_iff]
  intro x
  change x ∈ (realization n hn).torus.range ↔ _ ∈ (realization n hn).torus.range
  rw [(realization n hn).mem_range_iff, (realization n hn).mem_range_iff]
  simp only [map_mul, map_inv, RationalRealization.comparison_cycle]
  exact mem_normalizer_iff.mp (cycleWord_normalizes_rawTorus n) _

/-- Opposition inverts every element of the full rational torus. -/
theorem inverter_torusHom (n : ℕ) (hn : 0 < n) (a : Coordinates n) :
    (realization n hn).inverter * torusHom n hn a * (realization n hn).inverter⁻¹ =
      (torusHom n hn a)⁻¹ := by
  apply (realization n hn).comparison_injective
  simpa only [map_mul, map_inv, torusHom, RationalRealization.comparison_inverter,
    RationalRealization.comparison_torus] using inverterWord_rawTorus n a

theorem inverter_commutes_cycle (n : ℕ) (hn : 0 < n) :
    Commute (realization n hn).inverter (realization n hn).cycle := by
  apply (realization n hn).comparison_injective
  simp only [map_mul, RationalRealization.comparison_inverter,
    RationalRealization.comparison_cycle]
  exact (Commute.refl coxeter).pow_pow 3 2

/-- The actual Sylow-three subgroup, torus pair, cycle and inverter, with all
algebraic and rational-descent premises discharged. -/
theorem configuration_nonempty (n : ℕ) (hn : 0 < n) :
    Nonempty (Configuration (torus n hn)) :=
  (realization n hn).configuration (weylLaws n)

/-- The full nonsplit torus configuration, including every three-adic valuation
and the parameter q=2. -/
theorem exists_configuration (n : ℕ) (hn : 0 < n) :
    ∃ A : Subgroup (Standard.BinaryCarrier n hn),
      Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧ Nonempty (Configuration A) :=
  ⟨torus n hn, card_torus n hn, configuration_nonempty n hn⟩

/-- The nonsplit branch supplies the actual ambient Sylow-three geometry. -/
theorem geometry (n : ℕ) (hn : 0 < n) (hd : 3 ∣ 2 ^ n + 1) :
    Geometry 3 (Standard.BinaryCarrier n hn) :=
  (realization n hn).geometry (weylLaws n) hd

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
