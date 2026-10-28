module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.QuadraticSource
public import Theory.Representation.QuadraticFourGroup.TensorOddCommutator

/-!
# The original-module displacement bound from an odd component commutator

Perfectness and faithfulness supply an actual nontrivial irreducible section
of the component orbit. The genuine quadratic four-group theorem identifies
that section as a natural tensor along the original quotient. Applying the
odd-factor commutator bound gives the source numerical estimate in the
original module. No invariant section for the normalizing actor is assumed.

Source: GLS volume 2, Chapter G, Theorems 25.14 and 26.24, final paragraph.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.OddCommutatorSource
open Representation.QuadraticFourGroup
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- The actor has displacement at least twice the field degree whenever a
literal commutator projects to a nonidentity odd element in the first factor. -/
theorem two_mul_degree_le_fixedCodim (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B))
    (x : componentOrbit L B) (g : Factor M.n) (hg : M.projection x = (g,1))
    (ho : Odd (orderOf g)) (hne : g ≠ 1)
    (c l : G) (hx : (x : G) = c * l * c⁻¹ * l⁻¹) :
    2 * M.n ≤ fixedCodim ρ (zpowers c) := by
  let E := componentOrbit L B
  let τ := ρ.comp E.subtype
  let : Group.IsPerfect E := h.orbit_properties.1
  let : Group.IsPerfect (Factor M.n) :=
    Group.IsPerfect.ofSurjective
      (f := (MonoidHom.fst (Factor M.n) (Factor M.n)).comp M.projection)
      ((show Function.Surjective (MonoidHom.fst (Factor M.n) (Factor M.n)) from
        fun z => ⟨(z,1),rfl⟩).comp M.projection_surjective)
  have he : Function.Injective τ := h.faithful.comp E.subtype_injective
  have ht : ¬ (⊤ : Subgroup E) ≤ τ.ker := by
    intro ht
    have hxx := ht (mem_top x)
    rw [(MonoidHom.ker_eq_bot_iff _).mpr he, mem_bot] at hxx
    have hx1 : x = 1 := hxx
    have hgone : g = 1 := by
      have hh := congrArg Prod.fst hg.symm
      rw [hx1, map_one] at hh
      exact hh
    exact hne hgone
  obtain ⟨U,N,hi,hn⟩ := exists_irreducible_section_surviving_perfect (ρ := τ) ⊤ ht
  let σ := N.quotientRepresentation
  have hs : IsIrreducibleSection τ σ := ⟨hi,U,N,⟨Representation.Equiv.refl _⟩⟩
  have hsne : ¬ σ.IsTrivial := by
    intro hh
    apply hn
    intro y _
    exact hh.1 y
  have hnat := QuadraticSource.naturalTensorSection h M σ hs hsne
  exact hnat.first_odd_commutator_bound ρ E.subtype hs (by have := M.one_lt; omega)
    x g hg ho hne c l hx
end CFSG.Quasithin.ChapterB.ComponentNormalization.OddCommutatorSource
