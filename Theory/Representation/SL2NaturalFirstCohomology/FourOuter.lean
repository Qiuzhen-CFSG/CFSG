module
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
import Mathlib.Tactic.Abel

/-!
# A Frobenius actor and the natural SL₂(4) first cohomology

Suppose a binary representation restricts to the actual natural SL₂(4) module
on a normal image. Restriction on H¹ is injective because this natural module
has no fixed vectors. A normalizing actor induces a map on the restricted H¹,
and the cocycle identity shows that this map fixes all restricted classes.

When the actor is Frobenius-semilinear on the coefficients, its induced map is
Frobenius-semilinear as well. The explicit natural-module calculation identifies
H¹(SL₂(4), V) with one copy of F₄. If the ambient binary H¹ had dimension two,
restriction would be surjective; semilinearity would then force Frobenius to fix
every scalar. Thus the ambient dimension is at most one. This avoids choosing
a scalar for the outer action on the square-root cocycle parameter.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3) and J.2.5, printed pp.432 and 434 (PDF pp.443 and 445).
The natural-module H¹ calculation is I.1.6(2), printed p.408.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2NaturalH1.FourOuter
open Representation.OneCohomology SL2FourNatural
abbrev natRep : Representation F SL V := specialLinearNatural 2
variable {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
  (ι : SL →* G) (hr : ∀ g v, ρ (ι g) v = action g v)

def restrictionCocycles : cocycles ρ →ₗ[ZMod 2] cocycles natRep where
  toFun f := ⟨fun g => f.val (ι g), by
    intro g h
    simpa only [map_mul, hr, action_natural] using f.property (ι g) (ι h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restriction_principal (v : V) :
    restrictionCocycles ρ ι hr (principal ρ v) = principal natRep v := by
  apply Subtype.ext
  funext g
  exact congrArg (fun w => w - v) (hr g v)

def restriction : H1 ρ →ₗ[ZMod 2] H1 natRep :=
  (principal ρ).range.liftQ
    (((classMap natRep).restrictScalars (ZMod 2)).comp (restrictionCocycles ρ ι hr)) (by
      rintro _ ⟨v, rfl⟩
      change classMap natRep (restrictionCocycles ρ ι hr (principal ρ v)) = 0
      rw [restriction_principal]
      exact (classMap_eq_zero_iff _ _).mpr ⟨v, rfl⟩)

lemma restriction_class (f : cocycles ρ) :
    restriction ρ ι hr (classMap ρ f) =
      classMap natRep (restrictionCocycles ρ ι hr f) := rfl

lemma restriction_injective
    (hn : ∀ (g : G) (x : SL), ∃ y : SL, ι x * g = g * ι y) :
    Function.Injective (restriction ρ ι hr) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨f, rfl⟩ := (principal ρ).range.mkQ_surjective z
  obtain ⟨v, hv⟩ := (classMap_eq_zero_iff natRep _).mp hz
  let q := f - principal ρ v
  have hq (x : SL) : q.val (ι x) = 0 := by
    have he := congrArg (fun f : cocycles natRep => f.val x) hv
    change action x v - v = f.val (ι x) at he
    change f.val (ι x) - (ρ (ι x) v - v) = 0
    rw [hr, he, sub_self]
  have hzero : q = 0 := by
    apply Subtype.ext
    funext g
    apply natural_fixed_eq_zero
    intro x
    obtain ⟨y, hy⟩ := hn g x
    have he := congrArg q.val hy
    rw [q.property, q.property, hq, hq, map_zero, zero_add, add_zero, hr] at he
    exact he
  have hf : f = principal ρ v := sub_eq_zero.mp hzero
  exact (classMap_eq_zero_iff ρ f).mpr ⟨v, hf.symm⟩

variable (t : G) (σ : SL →* SL)
  (hc : ∀ g, t * ι (σ g) = ι g * t)
  (ht : ∀ (a : F) (v : V), ρ t (a • v) = fieldFrobenius a • ρ t v)

include hr hc in
lemma actor_intertwines (g : SL) (v : V) :
    ρ t (action (σ g) v) = action g (ρ t v) := by
  rw [← hr, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hr]

def outerCocycles : cocycles natRep →ₛₗ[fieldFrobenius.toRingHom] cocycles natRep where
  toFun f := ⟨fun g => ρ t (f.val (σ g)), by
    intro g h
    dsimp only
    rw [map_mul, f.property, map_add]
    change ρ t (action (σ g) (f.val (σ h))) + ρ t (f.val (σ g)) = _
    rw [actor_intertwines ρ ι hr t σ hc]
    rfl⟩
  map_add' f q := by apply Subtype.ext; funext g; exact map_add (ρ t) _ _
  map_smul' a f := by apply Subtype.ext; funext g; exact ht a (f.val (σ g))

lemma outer_principal (v : V) :
    outerCocycles ρ ι hr t σ hc ht (principal natRep v) = principal natRep (ρ t v) := by
  apply Subtype.ext
  funext g
  change ρ t (action (σ g) v - v) = action g (ρ t v) - ρ t v
  rw [map_sub, actor_intertwines ρ ι hr t σ hc]

def outerH1 : H1 natRep →ₛₗ[fieldFrobenius.toRingHom] H1 natRep :=
  (principal natRep).range.mapQ (principal natRep).range (outerCocycles ρ ι hr t σ hc ht) (by
    rintro _ ⟨v, rfl⟩
    exact ⟨ρ t v, (outer_principal ρ ι hr t σ hc ht v).symm⟩)

lemma outer_restriction (z : H1 ρ) :
    outerH1 ρ ι hr t σ hc ht (restriction ρ ι hr z) = restriction ρ ι hr z := by
  obtain ⟨f, rfl⟩ := (principal ρ).range.mkQ_surjective z
  have he : outerCocycles ρ ι hr t σ hc ht (restrictionCocycles ρ ι hr f) =
      restrictionCocycles ρ ι hr f + principal natRep (f.val t) := by
    apply Subtype.ext
    funext g
    have h := congrArg f.val (hc g)
    rw [f.property, f.property, hr] at h
    change ρ t (f.val (ι (σ g))) = f.val (ι g) + (action g (f.val t) - f.val t)
    rw [← add_sub_cancel_right (ρ t (f.val (ι (σ g)))) (f.val t), h]
    abel
  change classMap natRep (outerCocycles ρ ι hr t σ hc ht (restrictionCocycles ρ ι hr f)) = _
  rw [he, map_add, (classMap_eq_zero_iff _ _).mpr ⟨f.val t, rfl⟩, add_zero]
  rfl

include hr hc ht in
/-- A Frobenius-semilinear outer actor cuts the binary cohomology dimension to at most one. -/
theorem finrank_le_one [Finite G]
    (hn : ∀ (g : G) (x : SL), ∃ y : SL, ι x * g = g * ι y) :
    Module.finrank (ZMod 2) (H1 ρ) ≤ 1 := by
  have hcard : Nat.card F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card, card_field]
    rfl
  have hlarge : 2 < Nat.card F := by rw [hcard]; decide
  let e := (cohomologyEquiv (K := F) hlarge).restrictScalars (ZMod 2)
  have hd : Module.finrank (ZMod 2) (H1 natRep) = 2 := by
    rw [e.finrank_eq, field_finrank 2 hcard]
  have hi := restriction_injective ρ ι hr hn
  have hle := LinearMap.finrank_le_finrank_of_injective hi
  by_contra! h
  have heq : Module.finrank (ZMod 2) (H1 ρ) = Module.finrank (ZMod 2) (H1 natRep) := by omega
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hi
  have hfix (z : H1 natRep) : outerH1 ρ ι hr t σ hc ht z = z := by
    obtain ⟨x, rfl⟩ := hs z
    exact outer_restriction ρ ι hr t σ hc ht x
  obtain ⟨a, ha⟩ : ∃ a : F, fieldFrobenius a ≠ a := by decide +kernel
  let z : H1 natRep := e.symm 1
  have hz : z ≠ 0 := by
    intro hz
    have := congrArg e hz
    simp [z] at this
  apply ha
  apply smul_left_injective F hz
  calc
    fieldFrobenius a • z = outerH1 ρ ι hr t σ hc ht (a • z) := by
      rw [map_smulₛₗ, hfix]; rfl
    _ = a • z := hfix _
end Representation.SL2NaturalH1.FourOuter
