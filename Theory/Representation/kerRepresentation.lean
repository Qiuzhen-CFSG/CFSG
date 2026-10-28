module

public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

open MonoidHom Function

section kerLift'

namespace QuotientGroup


/-- The induced homomorphism from the quotient by the kernel of `φ`. -/
def kerLift' {G : Type*} [Group G] {H : Type*} [Monoid H] (φ : G →* H) :
    G ⧸ φ.ker →* H := lift _ φ fun _g => mem_ker.mp

theorem kerLift'_injective {G : Type*} [Group G] {H : Type*} [Monoid H]
    (φ : G →* H) : Injective (kerLift' φ) :=
  fun a b =>
    Quotient.inductionOn₂' a b
      fun a b (h : φ a = φ b) =>
        Quotient.sound' <| by
          rw [leftRel_apply, mem_ker, map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

end QuotientGroup

end kerLift'

section kerRepresentation

open QuotientGroup Representation

namespace Representation

open _root_.Representation

/-- The faithful quotient representation obtained by modding out the kernel of `ρ`. -/
def kerRepresentation {F G V : Type*} [CommSemiring F] [Group G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) : Representation F (G ⧸ ker ρ) V :=
  kerLift' ρ

theorem kerRepresentation_apply {F G V : Type*} [CommSemiring F] [Group G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V) (g : G)
    : Representation.kerRepresentation ρ (mk' _ g) = ρ g := by rfl

theorem kerRepresentation_faithful {F G V : Type*} [CommSemiring F] [Group G]
    [AddCommMonoid V] [Module F V] (ρ : Representation F G V) :
    Injective (kerRepresentation ρ) :=
  kerLift'_injective ρ

/-- The subrepresentation lattice is unchanged after passing to the faithful kernel quotient. -/
def kerRepresentationOrderIso {F G V : Type*} [CommRing F] [Group G] [AddCommMonoid V]
    [Module F V] (ρ : Representation F G V)
    : Subrepresentation (kerRepresentation ρ) ≃o Subrepresentation ρ :=
  {
    toFun :=
      fun φ =>
        .mk (φ.toSubmodule)
          (fun g v hv => by
            have := φ.apply_mem_toSubmodule (mk' _ g)
            rw [kerRepresentation_apply] at this
            exact this hv)
    invFun :=
      fun φ =>
        .mk (φ.toSubmodule)
          (fun g v hv => by
            have := φ.apply_mem_toSubmodule g.out hv
            rw [← kerRepresentation_apply] at this
            simp only [QuotientGroup.mk'_apply, Quotient.out_eq] at this
            exact this)
    map_rel_iff' := by rfl
  }

theorem kerRepresentation_irreducible_iff {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    : IsIrreducible (kerRepresentation ρ) ↔ IsIrreducible ρ :=
  OrderIso.isSimpleOrder_iff (kerRepresentationOrderIso ρ)

instance kerRepresentation_irreducible {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) [IsIrreducible ρ]
    : IsIrreducible (kerRepresentation ρ) :=
  (kerRepresentation_irreducible_iff ρ).mpr inferInstance

end Representation

end kerRepresentation
