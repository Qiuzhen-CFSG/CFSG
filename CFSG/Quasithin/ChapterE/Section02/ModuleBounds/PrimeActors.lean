module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearTwo
public import Theory.Representation.BinaryPrimeDegree.Quotient
public import Theory.Representation.SymplecticFour.BinaryDegree
public import Theory.Representation.Suzuki.BinaryDegree

/-!
# The symplectic and Suzuki degree bounds on the actual source module

Conjugation on the original P/Z has kernel inside O₂(X/Z). Consequently
every odd prime divisor of the original maximal-core quotient X/J divides the order of its
literal faithful action image. The binary general-linear order bound and
primitive divisors give degree at least 4k for Sp₄(2^k) and Sz(2^k).
The exact complementary-summand identity then gives actor rank at least 2k.

Only the source’s actual X/J group equivalences are supplied. The module need
not factor through the two-core, and neither a constituent classifier nor
a lower-degree certificate is assumed. Source: Aschbacher–Smith E.2.13(4),
combined manuscript (1 March 2004), printed pp.224–225.
-/

@[expose] public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

private theorem normalRepresentation_kernel {H : Type*} [Group H]
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U] :
    (normalRepresentation U).ker = centralizer (U : Set H) := by
  ext h
  constructor
  · intro hh u hu
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive U) =>
      ((f (Additive.ofMul ⟨u,hu⟩)).toMul : H)) hh
    change h * u * h⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change h * (v.toMul : H) * h⁻¹ = v.toMul
    rw [← hh _ v.toMul.property, mul_inv_cancel_right]

variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- An odd prime in the actual two-core quotient forces its binary order
as a lower bound for the original P/Z dimension. -/
theorem maximal_core_prime_degree (h : Hypotheses T V M g)
    (hfit : generalizedFitting X = pCore 2 X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    p ∣ Nat.card (X ⧸ J M) →
      orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (Additive ((P V M g).map q)) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  dsimp only
  intro hd
  have hker : ((normalRepresentation U).comp q).ker ≤ J M := by
    change (normalRepresentation U).ker.comap q ≤ J M
    rw [normalRepresentation_kernel]
    exact (h.quotient_core_centralizer_le hfit).trans h.twoCore_le_J
  exact Representation.BinaryPrimeDegree.orderOf_le_finrank_of_kernel_le
    ((normalRepresentation U).comp q) (J M) hker hp hp2
    (by simpa only [index_eq_card] using hd)

/-- The Sp₄ clause of E.2.13(4), on the original A/Z actor quotient. -/
theorem actor_rank_ge_symplectic_four
    {F : Type*} [Field F] [Finite F]
    (h : Hypotheses T V M g) (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2 ^ m) :
    letI := h.Z_normal
    ∀ _e : (X ⧸ J M) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F,
      2 * m ≤ Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  let := h.Z_normal
  intro e
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul hm
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at ho
    omega
  have hd := h.maximal_core_prime_degree hfit hp hp2 (by
    rw [Nat.card_congr e.toEquiv]
    exact Representation.SymplecticFour.prime_dvd_card_of_orderOf_two hm hcard hp ho)
  rw [ho, h.quotient_core_finrank_eq_twice_actor] at hd
  omega

/-- The Suzuki clause of E.2.13(4), with the original defining exponent 2m+1. -/
theorem actor_rank_ge_suzuki
    (h : Hypotheses T V M g) (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 1 ≤ m) :
    letI := h.Z_normal
    ∀ _e : (X ⧸ J M) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m,
      2 * (2 * m + 1) ≤ Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  let := h.Z_normal
  intro e
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul (by omega : 0 < 2*m+1)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at ho
    omega
  have hd := h.maximal_core_prime_degree hfit hp hp2 (by
    rw [Nat.card_congr e.toEquiv]
    exact Representation.Suzuki.prime_dvd_card_of_orderOf_two hm hp ho)
  rw [ho, h.quotient_core_finrank_eq_twice_actor] at hd
  omega
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
