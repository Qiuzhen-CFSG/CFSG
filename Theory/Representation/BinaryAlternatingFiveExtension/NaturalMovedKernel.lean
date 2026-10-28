module
public import Theory.Representation.BinaryAlternatingFiveExtension.NaturalKernelSection
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Exact moved-subgroup kernels for natural symmetric-five sections

The range of a marked natural subspace, viewed multiplicatively in the
ambient group, is the actual commutator subgroup when its linear range is
the corresponding commutator space. This removes the range-conversion
premise from the natural-kernel section theorem used in 10.2.1.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryPermutation.AlternatingFiveExtension
variable {G : Type*} [Group G]

theorem ambientNaturalMap_range_eq_commutator
    (U B : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U)
    (hr : s.range = Representation.NormalElementaryQuotient.commutatorSpace U B) :
    (ambientNaturalMap U s).range = ⁅U,B⁆ := by
  apply le_antisymm
  · rintro x ⟨v,rfl⟩
    have hv : s v.toAdd ∈ Representation.NormalElementaryQuotient.commutatorSpace U B :=
      hr ▸ (show s v.toAdd ∈ s.range from ⟨v.toAdd,rfl⟩)
    exact hv
  · intro x hx
    have hxu : x ∈ U := (commutator_le_left U B) hx
    have hv : Additive.ofMul (⟨x,hxu⟩ : U) ∈ s.range := by
      rw [hr]
      exact hx
    obtain ⟨v,hv⟩ := hv
    exact ⟨Multiplicative.ofAdd v,congrArg (fun z : Additive U => (z.toMul : G)) hv⟩

/-- A literal commutator kernel and its natural linear marking supply a
section of the prescribed symmetric-five epimorphism. -/
theorem exists_section_of_natural_commutator_range [Finite G]
    (U B P : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : P →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (hr : s.range = Representation.NormalElementaryQuotient.commutatorSpace U B)
    (hk : q.ker.map P.subtype = ⁅U,B⁆)
    (he : ∀ (g : P) (v : core (Fin 5)),
      ((s (coreRepresentation (Fin 5) (q g) v)).toMul : G) =
        (g : G) * ((s v).toMul : G) * (g : G)⁻¹) :
    ∃ σ : Equiv.Perm (Fin 5) →* P, q.comp σ = MonoidHom.id _ :=
  exists_section_of_natural_range U P q hq s hs
    (hk.trans (ambientNaturalMap_range_eq_commutator U B s hr).symm) he

end BinaryPermutation.AlternatingFiveExtension
