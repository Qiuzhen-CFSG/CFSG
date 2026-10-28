module
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cubic fixed length of natural SL₂(4) copies

A nonidentity cubic matrix fixes only zero on the natural plane in
characteristic two. Apply this fact on each coordinate of the supplied
linear equivalence: s natural planes over the four-element field have
fixed index 4^(2s), hence cubic length 2s.

The restriction theorem retains the original actor map and natural
coordinates. An actor of order three embeds through a two-group kernel,
so the same calculation applies to the actual restricted action used on
the upper section in Aschbacher–Smith13.5.22, printed p.924.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryFixedPoints
variable {A : Type*} {B : Type*} {E : Type*} {F : Type*} [Group A] [Group B]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Field F] [CharP F 2] [Finite F] [Module (ZMod 2) F]

/-- Cubic actors have no nonzero fixed vector on a sum of natural planes. -/
theorem sl2_four_fixed_eq_bot
    (σ : Representation (ZMod 2) A E) (f : A →* SL(2,F))
    (hf : Nat.card f.range = 3) (s : ℕ)
    (q : E ≃ₗ[ZMod 2] (Fin s → Fin 2 → F))
    (heq : ∀ a v j, q (σ a v) j = Matrix.mulVec (f a).val (q v j)) :
    letI := action σ
    FixedPoints.subgroup A (Multiplicative E) = ⊥ := by
  let := action σ
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 3 (by rw [hf])
  obtain ⟨a,ha⟩ := g.property
  have ho : orderOf (f a) = 3 := by
    rw [ha]
    exact (orderOf_injective _ f.range.subtype_injective g).trans hg
  apply le_bot_iff.mp
  intro v hv
  have hzero : q v.toAdd = 0 := by
    funext j
    exact Matrix.SL2.cubic_fixed_eq_zero (f a) ho (q v.toAdd j)
      ((heq a v.toAdd j).symm.trans (congrArg (fun w => q w j) (hv a)))
  have hz : v.toAdd = 0 := q.injective (hzero.trans q.map_zero.symm)
  exact hz

/-- Each natural SL₂(4) plane contributes two to the actual cubic fixed length. -/
theorem sl2_four_cubicLength
    (σ : Representation (ZMod 2) A E) (f : A →* SL(2,F))
    (hf : Nat.card f.range = 3) (hF : Nat.card F = 4) (s : ℕ)
    (q : E ≃ₗ[ZMod 2] (Fin s → Fin 2 → F))
    (heq : ∀ a v j, q (σ a v) j = Matrix.mulVec (f a).val (q v j)) :
    letI := action σ
    FixedPoints.cubicLength A (Multiplicative E) = 2*s := by
  let := action σ
  have hc : Nat.card E = 4^(2*s) := by
    rw [Nat.card_congr q.toEquiv,Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_fin,hF,pow_mul]
  unfold FixedPoints.cubicLength
  rw [sl2_four_fixed_eq_bot σ f hf s q heq,Subgroup.index_bot]
  change Nat.log 4 (Nat.card E) = 2*s
  rw [hc,Nat.log_pow (by decide : 1 < 4)]

/-- The original actor of order three survives every two-group kernel;
the given natural coordinates retain its actual action after restriction. -/
theorem sl2_four_cubicLength_of_two_kernel [Finite A]
    (σ : Representation (ZMod 2) B E) (f : A →* B)
    (hA : Nat.card A = 3) (hf : IsPGroup 2 f.ker)
    (m : B ≃* SL(2,F)) (hF : Nat.card F = 4) (s : ℕ)
    (q : E ≃ₗ[ZMod 2] (Fin s → Fin 2 → F))
    (heq : ∀ b v j, q (σ b v) j = Matrix.mulVec (m b).val (q v j)) :
    letI := action (σ.comp f)
    FixedPoints.cubicLength A (Multiplicative E) = 2*s := by
  have h3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) hA
  have hb : f.ker = ⊥ := by
    simpa only [inf_idem] using
      (IsPGroup.disjoint_of_coprime hf (h3.to_subgroup f.ker) (by decide)).eq_bot
  have hi : Function.Injective (m.toMonoidHom.comp f) :=
    m.injective.comp ((MonoidHom.ker_eq_bot_iff f).mp hb)
  have hc : Nat.card (m.toMonoidHom.comp f).range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hA
  exact sl2_four_cubicLength (σ.comp f) (m.toMonoidHom.comp f) hc hF s q
    (fun a v j => heq (f a) v j)
end Representation.BinaryFixedPoints
