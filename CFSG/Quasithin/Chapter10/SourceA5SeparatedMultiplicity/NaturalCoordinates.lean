module

public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.ActorRank
public import Theory.Representation.AlternatingFive.AmplifiedNatural.Realization

/-!
# Natural coordinates discharge the separated-block displacement premises

The same permutation coordinates of the marked conjugation action are used
both to normalize each actual A₅ support action and to measure the projected
actor ranks. Equivariant homogeneous natural coordinates then supply all four
displacement inequalities required by the starred-actor multiplicity theorem.

This is the natural-module branch of the multiplicity step in Aschbacher--Smith
D.3.9 and D.3.21. The earlier-source coordinate and support constructions remain
explicit; the amplified displacement premises are proved here.
-/

@[expose] public noncomputable section
open Subgroup Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open Representation.AlternatingFive
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
open Theory.GroupTheory.WreathTwoElementaryRank
namespace CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [CharP F 2] [Finite F]
variable {A V : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite A] in
/-- Natural homogeneous coordinates supply both projected displacement bounds. -/
theorem natural_block_bounds
    (hF : Nat.card F = 4)
    (τ : Representation (ZMod 2) A V) (p : A →* Sym)
    (ρ : Representation (ZMod 2) Alt V) {k : ℕ}
    (e : AmplifiedNatural.Coordinates F (ι := Fin k) ρ)
    (hc : ∀ a g v, τ a (ρ g v) = ρ (MulAut.conjNormal (p a) g) (τ a v)) :
    (∀ a, p a ≠ 1 → k ≤ operatorFixedCodim (τ a)) ∧
    (∀ a, p a ≠ 1 → p a ∈ Alt → 2 * k ≤ operatorFixedCodim (τ a)) := by
  have bound (a : A) (ha : p a ≠ 1) : 2 * k ≤ operatorFixedCodim (τ a) := by
    have ha2 : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
    have hp2 : p a * p a = 1 := by
      simpa only [map_pow, map_one, pow_two, map_mul] using congrArg p ha2
    have hi : Function.Injective (τ a) := (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom a)).injective
    simpa only [Fintype.card_fin] using e.nontrivial_bound hF (τ a) hi (p a) hp2 ha (hc a)
  exact ⟨fun a ha => (by omega : k ≤ 2 * k).trans (bound a ha),
    fun a ha _ => bound a ha⟩

/-- Build the exact preserved-block input from the actual natural coordinate
maps and their literal factor-conjugation equations. -/
def PreservedBlocks.of_natural (hF : Nat.card F = 4)
    (τ : Representation (ZMod 2) A V) (f : A →* W Sym) (k : ℕ)
    (hb : ∀ a, (f a).right = 1)
    (B₁ B₂ : Subrepresentation τ)
    (e : V ≃ₗ[ZMod 2] B₁.toSubmodule × B₂.toSubmodule)
    (he : ∀ a v, e (τ a v) =
      (B₁.toRepresentation a (e v).1, B₂.toRepresentation a (e v).2))
    (ρ₁ : Representation (ZMod 2) Alt B₁.toSubmodule)
    (ρ₂ : Representation (ZMod 2) Alt B₂.toSubmodule)
    (e₁ : AmplifiedNatural.Coordinates F (ι := Fin k) ρ₁)
    (e₂ : AmplifiedNatural.Coordinates F (ι := Fin k) ρ₂)
    (hc₁ : ∀ a g v, B₁.toRepresentation a (ρ₁ g v) =
      ρ₁ (MulAut.conjNormal ((f a).left 1) g) (B₁.toRepresentation a v))
    (hc₂ : ∀ a g v, B₂.toRepresentation a (ρ₂ g v) =
      ρ₂ (MulAut.conjNormal ((f a).left turn) g) (B₂.toRepresentation a v)) :
    PreservedBlocks τ f k hb := by
  let p := preservedPairHom f hb
  let f₁ := (MonoidHom.fst Sym Sym).comp p
  let f₂ := (MonoidHom.snd Sym Sym).comp p
  have hp₁ (a : A) : f₁ a = (f a).left 1 :=
    congrArg Prod.fst (preservedPairHom_apply f hb a)
  have hp₂ (a : A) : f₂ a = (f a).left turn :=
    congrArg Prod.snd (preservedPairHom_apply f hb a)
  have h₁ := natural_block_bounds F hF B₁.toRepresentation f₁ ρ₁ e₁
    (by intro a g v; rw [hp₁]; exact hc₁ a g v)
  have h₂ := natural_block_bounds F hF B₂.toRepresentation f₂ ρ₂ e₂
    (by intro a g v; rw [hp₂]; exact hc₂ a g v)
  exact {
    first := B₁
    second := B₂
    coordinates := e
    intertwines := he
    first_nontrivial := by simpa only [hp₁] using h₁.1
    first_inner := by simpa only [hp₁] using h₁.2
    second_nontrivial := by simpa only [hp₂] using h₂.1
    second_inner := by simpa only [hp₂] using h₂.2 }

end CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
