module

public import Mathlib.RepresentationTheory.Character
public import Theory.Representation.CompleteReducibility
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Representations determined by their characters

Finite-dimensional representations of a finite group over a characteristic-zero
field are equivalent if their trace characters agree. Induct on dimension, choose
an irreducible subrepresentation, and use the character formula for intertwiner
dimensions to embed it in the other representation. Maschke's theorem splits both
embeddings; cancellation of characters permits induction on the complements.

The usual character criterion is presented over the complex numbers in Serre,
*Linear Representations of Finite Groups*, Chapter 2. The same argument here works
over every characteristic-zero field, without an algebraic-closure assumption.
-/

public section

open scoped MonoidAlgebra
open Representation
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Representation

variable {K G V W : Type*} [Field K] [CharZero K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
private theorem split_injection (ρ : Representation K G V) (σ : Representation K G W)
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i) :
    ∃ S : Subrepresentation ρ, Nonempty ((σ.prod S.toRepresentation).Equiv ρ) := by
  let : IsSemisimpleModule K[G] ρ.asModule :=
    ρ.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (Or.inl (ringChar.eq_zero (R := K)))
  obtain ⟨M, hM⟩ := exists_isCompl i.range.asSubmodule
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' M
  have hcompl : IsCompl i.range.toSubmodule S.toSubmodule :=
    (Submodule.isCompl_restrictScalars_iff K).mpr hM
  let e := Submodule.prodEquivOfIsCompl i.range.toSubmodule S.toSubmodule hcompl
  let j : W ≃ₗ[K] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  refine ⟨S, ⟨Representation.Equiv.mk
    ((j.prodCongr (LinearEquiv.refl K S.toSubmodule)).trans e) ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro x
  change i (σ g x.1) + ρ g x.2 = ρ g (i x.1 + x.2)
  rw [map_add, i.isIntertwining]

omit [Finite G] [CharZero K] in
/-- The character of a product is the sum of the characters. -/
theorem character_prod (ρ : Representation K G V) (σ : Representation K G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  ext g
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- Equal characters determine finite-dimensional representations of finite groups
over any characteristic-zero field. -/
theorem equiv_of_character_eq (ρ : Representation K G V) (σ : Representation K G W)
    (hchar : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  classical
  induction hn : Module.finrank K V using Nat.strong_induction_on generalizing V W with
  | h n ih =>
    by_cases hV : Subsingleton V
    · let := hV
      have hdim : Module.finrank K W = 0 := by
        have hc := congrFun hchar 1
        simp only [char_one, Module.finrank_zero_of_subsingleton, Nat.cast_zero] at hc
        exact_mod_cast hc.symm
      let : Subsingleton W := (Module.finrank_zero_iff).mp hdim
      exact ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W)
        (fun _ => Subsingleton.elim _ _)⟩
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
      let := hS
      let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
      let i : S.toRepresentation.IntertwiningMap ρ :=
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩
      have hi : Function.Injective i := Subtype.val_injective
      have hi0 : i ≠ 0 := by
        intro hz
        obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
        apply hx
        apply hi
        simp [hz]
      let : Fintype G := Fintype.ofFinite G
      let : Invertible (Nat.card G : K) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      have hhom : Module.finrank K (S.toRepresentation.IntertwiningMap ρ) =
          Module.finrank K (S.toRepresentation.IntertwiningMap σ) := by
        apply Nat.cast_injective (R := K)
        rw [← card_inv_mul_sum_char_mul_char_eq_finrank,
          ← card_inv_mul_sum_char_mul_char_eq_finrank, hchar]
      have hpos : 0 < Module.finrank K (S.toRepresentation.IntertwiningMap σ) := by
        rw [← hhom]
        exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨i, hi0⟩
      obtain ⟨j, hj0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
      have hj : Function.Injective j := (IsIrreducible.injective_or_eq_zero j).resolve_right hj0
      obtain ⟨C, ⟨eρ⟩⟩ := split_injection ρ S.toRepresentation i hi
      obtain ⟨D, ⟨eσ⟩⟩ := split_injection σ S.toRepresentation j hj
      have hc : C.toRepresentation.character = D.toRepresentation.character := by
        have he := (char_iso eρ).trans (hchar.trans (char_iso eσ).symm)
        rw [character_prod, character_prod] at he
        exact add_left_cancel he
      have hlt : Module.finrank K C.toSubmodule < n := by
        have he := eρ.toLinearEquiv.finrank_eq
        rw [Module.finrank_prod, hn] at he
        have hs := Module.finrank_pos (R := K) (M := S.toSubmodule)
        omega
      obtain ⟨e⟩ := ih _ hlt C.toRepresentation D.toRepresentation hc rfl
      let ep : (S.toRepresentation.prod C.toRepresentation).Equiv
          (S.toRepresentation.prod D.toRepresentation) :=
        Representation.Equiv.mk ((LinearEquiv.refl K S.toSubmodule).prodCongr e.toLinearEquiv)
          (fun g => by
            apply LinearMap.ext
            intro x
            apply Prod.ext
            · rfl
            · exact congrArg (fun f => f x.2) (e.toIntertwiningMap.isIntertwining' g))
      exact ⟨eρ.symm.trans (ep.trans eσ)⟩

end Representation
