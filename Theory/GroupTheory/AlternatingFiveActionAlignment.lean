module

public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Aligning a five-point action with a prescribed alternating quotient

Two actions with the same kernel, one onto A₅ and the other on five points,
differ by conjugation by one permutation. The latter action factors through
the prescribed quotient and is faithful there. Perfectness puts its image
inside A₅; finiteness makes this an automorphism, and Aut(A₅)=S₅ supplies
the conjugating permutation. The original quotient map is retained.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {L : Type*} [Group L]

/-- Align a five-point action to the literal A₅ quotient with the same kernel. -/
theorem exists_conjugating_perm_of_same_alternating_five_kernel
    (α : L →* Equiv.Perm (Fin 5)) (π : L →* alternatingGroup (Fin 5))
    (hπ : Function.Surjective π) (hker : α.ker = π.ker) :
    ∃ p : Equiv.Perm (Fin 5), ∀ l : L, α l = p * (π l).val * p⁻¹ := by
  let f : alternatingGroup (Fin 5) →* Equiv.Perm (Fin 5) :=
    π.liftOfSurjective hπ ⟨α,hker.symm.le⟩
  have hf (l : L) : f (π l) = α l := π.liftOfRightInverse_comp_apply _ _ _ l
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    obtain ⟨l,rfl⟩ := hπ a
    have hal : α l = 1 := (hf l).symm.trans ha
    have hl : l ∈ π.ker := hker ▸ hal
    exact hl
  have heven (a : alternatingGroup (Fin 5)) : f a ∈ alternatingGroup (Fin 5) := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    let s := Equiv.Perm.sign.comp f
    have hs : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ s.ker := by
      rw [←commutator_alternatingGroup_eq_top (by simp)]
      exact Abelianization.commutator_subset_ker s
    exact hs (mem_top a)
  let fA : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) := f.codRestrict _ heven
  have hfA : Function.Injective fA := fun a b h => hinj (congrArg Subtype.val h)
  let a : MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective fA ⟨hfA,Finite.surjective_of_injective hfA⟩
  obtain ⟨p,hp⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide)).surjective a
  refine ⟨p,?_⟩
  intro l
  have hh := congrArg (fun e : MulAut (alternatingGroup (Fin 5)) => (e (π l)).val) hp
  change p * (π l).val * p⁻¹ = f (π l) at hh
  exact ((hf l).symm.trans hh.symm)

end Theory.GroupTheory
