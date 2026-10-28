module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.Coefficients
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A central G₂ commutator from its root containment and torus action

This is the group-theoretic application of the coefficient argument in
Fong–Seitz II (9.16)(i)–(9.19), printed pp.216–217. The actual three root
homomorphisms live in one group. Central containment supplies the unknown
coefficient; commutator identities prove biadditivity, and conjugation by
the supplied torus supplies its scaling law. Only the commutator at the
unit parameters is normalized by the rank-one pinning.

The conclusion is the literal left-commutator and ordered EB exchange.
The input is still intermediate source data: obtaining the pinnings,
containment and unit normalization from (6E)(a) is a separate proof step
within the source reconstruction.
-/

@[expose] public noncomputable section
open scoped commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K Y : Type*} [Field K] [CharP K 2] [Finite K] [Group Y]

/-- Three pinned roots and their central containment and torus action. -/
structure CentralPairData (K Y : Type*) [Field K] [Group Y] where
  A : Multiplicative K →* Y
  B : Multiplicative K →* Y
  E : Multiplicative K →* Y
  A_injective : Function.Injective A
  ba : ∀ b a, Commute (B (.ofAdd b)) (A (.ofAdd a))
  ea : ∀ e a, Commute (E (.ofAdd e)) (A (.ofAdd a))
  commutator_mem : ∀ b e, ⁅E (.ofAdd e), B (.ofAdd b)⁆ ∈ A.range
  torus : Kˣ → Y
  torus_A : ∀ t a, torus t * A (.ofAdd a) * (torus t)⁻¹ =
    A (.ofAdd ((t : K)⁻¹ * a))
  torus_B : ∀ t b, torus t * B (.ofAdd b) * (torus t)⁻¹ =
    B (.ofAdd ((t : K) * b))
  torus_E : ∀ t e, torus t * E (.ofAdd e) * (torus t)⁻¹ =
    E (.ofAdd ((t : K)⁻¹ ^ 2 * e))
  unit_commutator : ⁅E (.ofAdd 1), B (.ofAdd 1)⁆ = A (.ofAdd 1)

omit [CharP K 2] [Finite K] in
private theorem parameter_add (r : Multiplicative K →* Y) (a b : K) :
    r (.ofAdd (a+b)) = r (.ofAdd a) * r (.ofAdd b) := r.map_mul _ _

namespace CentralPairData
variable (d : CentralPairData K Y)
/-- Central containment, root additivity and the torus force the product coefficient. -/
theorem commutator (b e : K) :
    ⁅d.E (.ofAdd e), d.B (.ofAdd b)⁆ = d.A (.ofAdd (b*e)) := by
  classical
  have hex : ∀ b e, ∃ c : K, ⁅d.E (.ofAdd e), d.B (.ofAdd b)⁆ = d.A (.ofAdd c) := by
    intro b e
    obtain ⟨c,hc⟩ := d.commutator_mem b e
    exact ⟨c.toAdd,hc.symm⟩
  choose f hf using hex
  have hi : Function.Injective (fun a : K => d.A (.ofAdd a)) :=
    d.A_injective.comp Multiplicative.ofAdd.injective
  have hfirst (a a' b : K) : f (a + a') b = f a b + f a' b := by
    apply hi
    dsimp only
    rw [← hf, parameter_add, commutatorElement_mul_right_eq_mul_conj,
      hf, hf, parameter_add]
    rw [mul_assoc (d.A _) (d.B _) (d.A _), (d.ba a (f a' b)).eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hsecond (a b b' : K) : f a (b + b') = f a b + f a b' := by
    apply hi
    dsimp only
    rw [← hf, parameter_add, commutatorElement_mul_left_eq_conj_mul,
      hf, hf, parameter_add, (d.ea b (f a b')).eq]
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← parameter_add, ← parameter_add, add_comm (f a b') (f a b)]
  have hscale (t : Kˣ) (a b : K) :
      f ((t : K) * a) ((t : K)⁻¹ ^ 2 * b) = (t : K)⁻¹ * f a b := by
    apply hi
    dsimp only
    rw [← hf, ← d.torus_E, ← d.torus_B, ← conjugate_commutatorElement,
      hf, d.torus_A]
  have hn : f 1 1 = 1 := hi ((hf 1 1).symm.trans d.unit_commutator)
  rw [hf, f_normalization f hfirst hsecond hscale, hn, mul_one]

/-- Conversion to the consumer's ordered exchange convention. -/
theorem exchange (b e : K) :
    d.E (.ofAdd e) * d.B (.ofAdd b) =
      d.A (.ofAdd (b*e)) * d.B (.ofAdd b) * d.E (.ofAdd e) := by
  rw [← d.commutator]
  simp [commutatorElement_def, mul_assoc]
end CentralPairData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
