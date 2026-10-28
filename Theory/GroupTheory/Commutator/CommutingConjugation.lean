module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Automorphisms commuting with conjugation on a subgroup

If an automorphism preserves U and commutes on U with conjugation by L,
it preserves [U,L]. It also preserves C_W(L) for each invariant W ≤ U.
The actor L itself need not be invariant: only its action on U matters.

The proof compares the images of individual commutators and then uses
surjectivity on U and W. No finiteness assumption is needed. This supplies
the scalar-lift normalization of the full module and root in the final
linear-three branch of Aschbacher–Smith 4.3.2, printed pp.618–619.
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

private theorem map_commutatorElement_of_conj_compatible
    (U L : Subgroup G) (f : MulAut G)
    (hf : ∀ l ∈ L, ∀ u ∈ U, f (l * u * l⁻¹) = l * f u * l⁻¹)
    {u l : G} (hu : u ∈ U) (hl : l ∈ L) :
    f ⁅u,l⁆ = ⁅f u,l⁆ := by
  calc
    f ⁅u,l⁆ = f u * f (l * u⁻¹ * l⁻¹) := by
      rw [← map_mul]
      congr 1
      simp only [commutatorElement_def, mul_assoc]
    _ = f u * (l * f u⁻¹ * l⁻¹) := by rw [hf l hl u⁻¹ (U.inv_mem hu)]
    _ = ⁅f u,l⁆ := by simp only [map_inv, commutatorElement_def, mul_assoc]

/-- An automorphism commuting with the actor on U preserves [U,L].
It need not preserve L as a subgroup of the ambient group. -/
theorem map_commutator_eq_of_conj_compatible
    (U L : Subgroup G) (f : MulAut G) (hU : U.map f.toMonoidHom = U)
    (hf : ∀ l ∈ L, ∀ u ∈ U, f (l * u * l⁻¹) = l * f u * l⁻¹) :
    (⁅U,L⁆).map f.toMonoidHom = ⁅U,L⁆ := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply commutator_le.mpr
    intro u hu l hl
    change f ⁅u,l⁆ ∈ ⁅U,L⁆
    rw [map_commutatorElement_of_conj_compatible U L f hf hu hl]
    exact commutator_mem_commutator (hU ▸ mem_map_of_mem f.toMonoidHom hu) hl
  · apply commutator_le.mpr
    intro u hu l hl
    obtain ⟨v,hv,rfl⟩ := hU.symm ▸ hu
    change ⁅f v,l⁆ ∈ (⁅U,L⁆).map f.toMonoidHom
    rw [← map_commutatorElement_of_conj_compatible U L f hf hv hl]
    exact mem_map_of_mem f.toMonoidHom (commutator_mem_commutator hv hl)

/-- The same compatibility preserves the fixed subgroup in every preserved
subgroup of U, without assuming that f preserves the actor. -/
theorem map_inf_centralizer_eq_of_conj_compatible
    (U A W : Subgroup G) (f : MulAut G) (hWU : W ≤ U)
    (hW : W.map f.toMonoidHom = W)
    (hf : ∀ a ∈ A, ∀ u ∈ U, f (a * u * a⁻¹) = a * f u * a⁻¹) :
    (W ⊓ centralizer (A : Set G)).map f.toMonoidHom = W ⊓ centralizer (A : Set G) := by
  have he (w : G) (hw : w ∈ U) :
      f w ∈ centralizer (A : Set G) ↔ w ∈ centralizer (A : Set G) := by
    simp only [mem_centralizer_iff_commutator_eq_one']
    constructor
    · intro hc a ha
      apply f.injective
      rw [map_commutatorElement_of_conj_compatible U A f hf hw ha, hc a ha, map_one]
    · intro hc a ha
      rw [← map_commutatorElement_of_conj_compatible U A f hf hw ha, hc a ha, map_one]
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact ⟨hW ▸ mem_map_of_mem f.toMonoidHom hw.1, (he w (hWU hw.1)).mpr hw.2⟩
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := hW.symm ▸ hw.1
    exact ⟨v,⟨hv, (he v (hWU hv)).mp hw.2⟩,rfl⟩
end Subgroup
