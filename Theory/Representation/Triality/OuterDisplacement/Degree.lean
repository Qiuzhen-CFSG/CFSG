module

public import Theory.Representation.Triality.PrimitiveDegree
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Triality degree bounds through arbitrary central covers

A primitive prime of binary order 12*n divides the genuine triality carrier.
Its divisibility passes from N/Z(N) to N and then to the ambient finite group.
A faithful representation, restricted to the binary field without changing
any operators, therefore has dimension at least 12*n. No restriction on the
center, normality, or irreducibility is needed for this transfer.

The model and primitive-prime calculations are those of `PrimitiveDegree`,
from GLS3 Sections 2.3--2.4 and GLS2 Chapter A, Theorem 1.1. This extension
provides the degree estimate for the outer-action branch of Guralnick--Malle,
*Classification of 2F-modules, II*, Lemma 8.6, internal pp.56--57.
-/

@[expose] public section

namespace Triality.OuterDisplacement

variable {E H W : Type*} [Field E] [Finite E] [Algebra (ZMod 2) E]
  [Group H] [Finite H] [AddCommGroup W] [Module E W] [FiniteDimensional E W]

/-- The primitive-prime degree bound passes through the literal central quotient
and retains the coefficient-field degree. -/
theorem degree_ge_of_central_quotient (σ : Representation E H W)
    (hσ : Function.Injective σ) (N : Subgroup H) (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ Subgroup.center N)) :
    12 * n ≤ Module.finrank (ZMod 2) E * Module.finrank E W := by
  let : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) E)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans E W
  let σ₂ : Representation (ZMod 2) H W := {
    toFun g := (σ g).restrictScalars (ZMod 2)
    map_one' := by ext v; exact congrArg (fun f : Module.End E W => f v) σ.map_one
    map_mul' g h := by ext v; exact congrArg (fun f : Module.End E W => f v) (σ.map_mul g h) }
  have hi : Function.Injective σ₂ := by
    intro g h he
    apply hσ
    ext v
    exact congrArg (fun f : Module.End (ZMod 2) W => f v) he
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  obtain ⟨p, hp, hp2, hdiv, ho⟩ := PrimitiveDegree.exists_prime_dvd_card n hn
  have hd : p ∣ Nat.card H := by
    rw [← Nat.card_congr e.toEquiv] at hdiv
    exact hdiv.trans ((Subgroup.center N).card_quotient_dvd_card.trans
      N.card_subgroup_dvd_card)
  have hb := Representation.BinaryPrimeDegree.orderOf_le_finrank σ₂ hi hp hp2 hd
  rw [ho, ← Module.finrank_mul_finrank (ZMod 2) E W] at hb
  exact hb

end Triality.OuterDisplacement
