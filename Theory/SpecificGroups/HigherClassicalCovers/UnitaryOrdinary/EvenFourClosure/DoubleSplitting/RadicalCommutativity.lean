module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.Setup
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity.Actions

/-!
# The lifted unitary-four plane radical is abelian

In a central extension, commutators above the Hermitian radical form a
biadditive pairing fixed by ambient conjugation. The full plane parabolic
contains a torus fixing one diagonal coordinate and moving the other diagonal
and off-diagonal coordinates. Its invariance, together with the elementary
SL₂ shears, kills the pairing. The source parameter n ≥ 2 supplies a nonzero
fixed scalar other than one, including when the fixed field is GF(4).

All maps are the original maps from `Setup`: the radical is the restriction
kernel inside the determinant-one local, then embedded in standard SU₄ and
pulled back through the covering map. The argument works for arbitrary central
kernels; the last theorems specialize to the requested double covers.

Source: Aschbacher–Smith I.1.3–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1. This supplies the radical-commutativity step, not the remaining
radical-section and multiplier assemblies.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting

universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

/-- The marked Hermitian parametrization has exactly the ambient radical as
its range; this retains both subgroup inclusions in `Setup`. -/
theorem unipotentMap_range (J : HermitianForm 4 F) :
    (RadicalCommutativity.unipotentMap F J.conj J.conj_involutive).range =
      ambientRadical J := by
  have hu : (UnitaryFourPlaneRadical.unipotent F J.conj J.conj_involutive).range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (UnitaryFourPlaneRadical.radicalEquiv F J.conj J.conj_involutive).surjective
  rw [RadicalCommutativity.unipotentMap, MonoidHom.range_comp, MonoidHom.range_comp,
    hu, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

omit [CharP F 2] in
/-- The source field parameters provide a nonzero fixed scalar other than one. -/
theorem exists_fixed_scalar (J : HermitianForm 4 F) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ c : FixedBy.subfield F J.conj, c ≠ 0 ∧ c ≠ 1 := by
  have hk : Nat.card (FixedBy.subfield F J.conj) = 2 ^ n :=
    UnitaryFourFormTransport.fixed_card J n (by omega) hcard hconj
  have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  apply ENat.exists_ne_ne_of_three_le _ 0 1
  rw [ENat.card_eq_coe_natCard, hk]
  exact_mod_cast (show 3 ≤ 2 ^ n by norm_num at hp; omega)

/-- Pointwise commutation above the literal ambient radical, for any central
covering. The full-parabolic calculation also covers the fixed field GF(4). -/
theorem commute_lifts_of_ambientRadical (J : HermitianForm 4 F)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type u} [Group E] (d : Cover E (Standard J))
    {a b : E} (ha : d.toMonoidHom a ∈ ambientRadical J)
    (hb : d.toMonoidHom b ∈ ambientRadical J) : Commute a b := by
  obtain ⟨c, hc, hc1⟩ := exists_fixed_scalar J n hn hcard hconj
  rw [← unipotentMap_range J] at ha hb
  obtain ⟨X, hX⟩ := ha
  obtain ⟨Y, hY⟩ := hb
  exact RadicalCommutativity.commute_unipotent_lifts F J.conj J.conj_involutive
    d.toMonoidHom d.surjective d.ker_le_center c hc hc1 X.toAdd Y.toAdd hX.symm hY.symm

/-- The full inverse image of the plane radical is abelian in each double
cover. In fact the proof needs neither the kernel-order bound nor perfectness. -/
theorem liftedRadical_isMulCommutative (J : HermitianForm 4 F)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type u} [Group E] [Finite E] (d : Cover E (Standard J))
    (_hd : Nat.card d.toMonoidHom.ker = 2) : IsMulCommutative (liftedRadical J d) where
  is_comm.comm a b := Subtype.ext
    (commute_lifts_of_ambientRadical J n hn hcard hconj d a.property b.property).eq

/-- An application to arbitrary chosen lifts of any two ambient-radical
elements, without identifying their subgroup carriers abstractly. -/
theorem doubleCover_lifts_commute (J : HermitianForm 4 F)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type u} [Group E] [Finite E] (d : Cover E (Standard J))
    (_hd : Nat.card d.toMonoidHom.ker = 2)
    (x y : ambientRadical J) {a b : E}
    (ha : d.toMonoidHom a = x) (hb : d.toMonoidHom b = y) : a * b = b * a :=
  (commute_lifts_of_ambientRadical J n hn hcard hconj d
    (by rw [ha]; exact x.property) (by rw [hb]; exact y.property)).eq

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
