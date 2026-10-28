module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OddReflection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanKernels

/-!
# The source reflection action on the entire Cartan

Conjugation by N descends through H = B ∩ N because H is abelian.
The simple Weyl classes therefore act involutorily on H even when an
arbitrary chosen lift does not have order two. The representative formula
uses right conjugation, as in Fong–Seitz. OddReflection gives the actual
fixed/inverted product equivalence and identifies the inverted factor
with the image of the displacement homomorphism.

These are the reflection decomposition and representative conventions
used in Fong–Seitz I (6H)(a), p.51. Identifying the fixed factor with the
panel kernel and comparing the two field parameters remain subsequent
source arguments. This module imposes no positive-parameter restriction.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual normalizer acts on the full Cartan subgroup. -/
def normalizerCartanAction : Q.tits.N →* MulAut (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  (Q.tits.B ⊓ Q.tits.N).normalizerMonoidHom.comp
    (inclusion (fun n hn => torus_normalizes (⟨n,hn⟩ : Q.tits.N)))

@[simp] theorem normalizerCartanAction_apply (n : Q.tits.N)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    (normalizerCartanAction Q n h : X ⧸ Q.D) = (n : X ⧸ Q.D)*h*(n : X ⧸ Q.D)⁻¹ := rfl

include split in
theorem cartan_le_action_kernel :
    (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N ≤ (normalizerCartanAction Q).ker := by
  let := split.abelian
  intro n hn
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  change (n : X ⧸ Q.D)*h*(n : X ⧸ Q.D)⁻¹ = h
  have he : (n : X ⧸ Q.D)*h = (h : X ⧸ Q.D)*n :=
    congrArg Subtype.val (mul_comm (⟨n,hn⟩ : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) h)
  rw [he, mul_inv_cancel_right]

def weylCartanAction : Weyl Q →* MulAut (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  QuotientGroup.lift ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
    (normalizerCartanAction Q) (cartan_le_action_kernel Q split)

@[simp] theorem weylCartanAction_lift (n : Q.tits.N) :
    weylCartanAction Q split
      (QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n) =
        normalizerCartanAction Q n := rfl

def simpleCartanAction (i : Fin 2) : MulAut (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  weylCartanAction Q split (Q.simple i)

theorem simpleCartanAction_involutive (i : Fin 2) :
    Function.Involutive (simpleCartanAction Q split i) := by
  intro h
  change ((weylCartanAction Q split (Q.simple i) *
    weylCartanAction Q split (Q.simple i)) h) = h
  rw [← map_mul, ← pow_two, (Q.tits.involutions _ (Q.simple_mem i)).2, map_one]
  rfl

/-- The source convention is right conjugation, with any lift of its simple class. -/
theorem simpleCartanAction_apply (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    (simpleCartanAction Q split i h : X ⧸ Q.D) = (n : X ⧸ Q.D)⁻¹*h*n := by
  have hs : (Q.simple i)⁻¹ = Q.simple i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
  have hn' : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n⁻¹ = Q.simple i := by
    rw [map_inv, hn, hs]
  change (weylCartanAction Q split (Q.simple i) h : X ⧸ Q.D) = _
  rw [← hn', weylCartanAction_lift, normalizerCartanAction_apply, coe_inv, inv_inv]

def reflectionFixed (i : Fin 2) : Subgroup (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  letI := split.abelian
  OddReflection.fixed (simpleCartanAction Q split i)

def reflectionInverted (i : Fin 2) : Subgroup (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  letI := split.abelian
  OddReflection.inverted (simpleCartanAction Q split i)

def reflectionDisplacement (i : Fin 2) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  letI := split.abelian
  OddReflection.displacement (simpleCartanAction Q split i)

theorem reflectionDisplacement_range (i : Fin 2) :
    (reflectionDisplacement Q split i).range = reflectionInverted Q split i := by
  let := split.abelian
  exact OddReflection.displacement_range (simpleCartanAction Q split i)
    (simpleCartanAction_involutive Q split i) split.odd

def cartanReflectionEquiv (i : Fin 2) :
    reflectionFixed Q split i × reflectionInverted Q split i ≃*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  letI := split.abelian
  OddReflection.productEquiv (simpleCartanAction Q split i)
    (simpleCartanAction_involutive Q split i) split.odd

@[simp] theorem cartanReflectionEquiv_apply (i : Fin 2)
    (a : reflectionFixed Q split i) (b : reflectionInverted Q split i) :
    (cartanReflectionEquiv Q split i (a,b) : X ⧸ Q.D) =
      (a.val : X ⧸ Q.D) * b.val := rfl

theorem cartan_card_reflection (i : Fin 2) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) =
      Nat.card (reflectionFixed Q split i) * Nat.card (reflectionInverted Q split i) := by
  rw [← Nat.card_congr (cartanReflectionEquiv Q split i).toEquiv, Nat.card_prod]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
