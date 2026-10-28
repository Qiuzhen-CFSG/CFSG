module

public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.Triality.Model.QTKEParameters

/-!
# The characteristic-two triality family

`BinaryCarrier f hf` is the genuine graph-field carrier `³D₄(2^f)`, for
`f > 0`, obtained by specializing `Standard.Carrier`. Thus its construction
uses the full D4 Cartan-plus-root lattice, the pinned arm cycle, and the
`2^f`-Frobenius over `GF(2^(3*f))`. It retains the elementary fixed-point
subgroup and central quotient of the standard construction.

`Triality.IsQTKETrialityModel` requires an actual multiplicative equivalence
to one of these finite groups. Unique prime-power parameters identify this
predicate with the characteristic-two part of the standard family. The
field-order bridge also fixes the exponent, so consumers can recover an
isomorphism to the specified carrier, including `³D₄(2)`.

Sources: Aschbacher–Smith, Theorem 0.1.2 and Remark A.2.4, with the `q = 2`
case in Theorem E (15.4.25), `refs/quasithin.pdf`; the construction and central
quotient conventions are GLS3 §§2.1–2.3, `refs/KGroup/GLS3/chapter2.tex`.
This is a model-membership interface, not a proof of the classification or
of quasithinness. The legacy `Triality.IsTrialityModel` describes a different
auxiliary group and supplies no input to these declarations.
-/

@[expose] public section

namespace Triality.Standard

/-- The actual finite triality carrier `³D₄(2^f)`, including `f = 1`. -/
abbrev BinaryCarrier (f : ℕ) (hf : 0 < f) := Carrier (binaryParameters f hf)

/-- A standard parameter with field order `2^f` is the specified binary parameter. -/
theorem Parameters.eq_binaryParameters_of_q_eq (P : Parameters) (f : ℕ)
    (hf : 0 < f) (hq : P.q = 2 ^ f) : P = binaryParameters f hf := by
  have hp : P.prime = 2 := by
    apply Nat.prime_eq_prime_of_dvd_pow P.prime_prime Nat.prime_two
    rw [← hq]
    exact dvd_pow_self _ (Nat.ne_of_gt P.exponent_pos)
  rcases P with ⟨p, e, hpprime, he⟩
  change p = 2 at hp
  subst p
  have heq : e = f := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hq
  subst e
  rfl

/-- Membership at a binary field order is exactly isomorphism to its binary carrier. -/
theorem isTrialityGroupAt_binary_iff (G : Type*) [Group G] (f : ℕ) (hf : 0 < f) :
    IsTrialityGroupAt (2 ^ f) G ↔ Nonempty (G ≃* BinaryCarrier f hf) := by
  constructor
  · rintro ⟨P, hq, h⟩
    have hP := P.eq_binaryParameters_of_q_eq f hf hq
    subst P
    exact h
  · intro h
    exact ⟨binaryParameters f hf, rfl, h⟩

/-- The smallest parameter in Theorem E uses the same genuine carrier. -/
theorem isTrialityGroupAt_two_iff (G : Type*) [Group G] :
    IsTrialityGroupAt 2 G ↔ Nonempty (G ≃* BinaryCarrier 1 (by decide)) := by
  simpa using isTrialityGroupAt_binary_iff G 1 (by decide)

end Triality.Standard

namespace Triality
open Standard

/-- The triality alternatives in the QTKE model list, with genuine group isomorphisms. -/
def IsQTKETrialityModel (G : Type*) [Group G] : Prop :=
  ∃ (f : ℕ) (hf : 0 < f), Nonempty (G ≃* BinaryCarrier f hf)

/-- Every positive binary exponent contributes its concrete carrier. -/
theorem isQTKETrialityModel_binaryCarrier (f : ℕ) (hf : 0 < f) :
    IsQTKETrialityModel (BinaryCarrier f hf) :=
  ⟨f, hf, ⟨MulEquiv.refl _⟩⟩

/-- Exactly the characteristic-two specialization of the standard triality family. -/
theorem isQTKETrialityModel_iff_characteristic_two (G : Type*) [Group G] :
    IsQTKETrialityModel G ↔
      ∃ P : Parameters, P.prime = 2 ∧ Nonempty (G ≃* Carrier P) := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨binaryParameters f hf, rfl, h⟩
  · rintro ⟨P, hp, h⟩
    obtain ⟨f, hf, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact ⟨f, hf, h⟩

/-- The binary field-order formulation of QTKE triality membership. -/
theorem isQTKETrialityModel_iff_fieldOrder (G : Type*) [Group G] :
    IsQTKETrialityModel G ↔ ∃ f : ℕ, 0 < f ∧ IsTrialityGroupAt (2 ^ f) G := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (isTrialityGroupAt_binary_iff G f hf).mpr h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (isTrialityGroupAt_binary_iff G f hf).mp h⟩

/-- The QTKE triality subfamily belongs to the full prime-power family. -/
theorem IsQTKETrialityModel.isTrialityGroup {G : Type*} [Group G]
    (h : IsQTKETrialityModel G) : IsTrialityGroup G := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨binaryParameters f hf, h⟩

/-- Transport membership by composing actual model isomorphisms. -/
theorem IsQTKETrialityModel.of_mulEquiv {G H : Type*} [Group G] [Group H]
    (h : IsQTKETrialityModel G) (e : H ≃* G) : IsQTKETrialityModel H := by
  obtain ⟨f, hf, ⟨a⟩⟩ := h
  exact ⟨f, hf, ⟨e.trans a⟩⟩

/-- Membership is invariant under group isomorphisms, also across universes. -/
theorem isQTKETrialityModel_mulEquiv_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : IsQTKETrialityModel G ↔ IsQTKETrialityModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- Finiteness follows from the concrete carrier, without an extra hypothesis. -/
theorem IsQTKETrialityModel.finite {G : Type*} [Group G]
    (h : IsQTKETrialityModel G) : Finite G := by
  obtain ⟨f, hf, ⟨e⟩⟩ := h
  exact Finite.of_injective e e.injective

end Triality
