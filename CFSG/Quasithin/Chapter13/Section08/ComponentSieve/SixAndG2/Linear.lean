module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.ModuleSieve
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Linear reductions for the A₆ component

The multiple-chief-factor argument of Aschbacher–Smith 13.8.26, printed
p.962, uses two separate intrinsic facts about the small module models:
a common commutator line forces a cyclic actor, and a transvection is the
entire pointwise centralizer of its fixed space. The critical-line sieve
and the larger critical actor then contradict a faithful submodule and
faithful quotient. We prove these deductions on the literal submodule
and quotient, with the two model facts and the absence of strong offenders
explicit. They are not asserted for arbitrary faithful representations.

The strong-offender contradiction also passes quadratic action to a
quotient of `V_H/U_H`. The surjection here must intertwine the actions;
an unrelated four-dimensional vector-space identification does not suffice.
The model recognition, marking by `L₁`, and cover identification remain
separate obligations before this can assert 13.8.26.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
open Representation.BinaryOffender

variable {H U B : Type*} [Group H] [Finite H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup B] [Module (ZMod 2) B]

omit [Finite H] in
theorem quadratic_on_equivariant_quotient
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H B)
    (q : U →ₗ[ZMod 2] B) (hq : Function.Surjective q)
    (he : ∀ g u, q (ρ g u) = σ g (q u))
    (A : Subgroup H) (hA : IsQuadratic ρ A) : IsQuadratic σ A := by
  intro a ha b hb v
  obtain ⟨u, rfl⟩ := hq v
  have h := congrArg q (hA a ha b hb u)
  simpa only [he, map_sub] using h

variable [FiniteDimensional (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

omit [Finite H] [FiniteDimensional (ZMod 2) U] in
private theorem subrepresentation_commutator_dim
    (W : Subrepresentation ρ) (A : Subgroup H) :
    Module.finrank (ZMod 2) (subspaceCommutator W.toRepresentation ⊤ A) =
      Module.finrank (ZMod 2) (subspaceCommutator ρ W.toSubmodule A) := by
  have he := subspaceCommutator_map_embedding ρ W.toRepresentation
    (MonoidHom.id H) W.toSubmodule.subtype (fun _ _ => rfl) A ⊤
  simp only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at he
  rw [he]
  exact (Submodule.equivMapOfInjective W.toSubmodule.subtype
    (Submodule.subtype_injective W.toSubmodule)
    (subspaceCommutator W.toRepresentation ⊤ A)).finrank_eq

/-- If the model excludes strong offenders and noncyclic groups with a
common commutator line, the critical-line sieve forces a cyclic actor. -/
theorem rank_one_of_no_strong_offenders
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U)
    (hS : IsAtom S) (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup H}
    (hA : IsElementaryTwo A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hstrongW : ¬ ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hstrongQ : ¬ ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B)
    (hlineW : ∀ B, IsElementaryTwo B →
      Module.finrank (ZMod 2) (subspaceCommutator W.toRepresentation ⊤ B) ≤ 1 → rank B = 1)
    (hlineQ : ∀ B, IsElementaryTwo B →
      Module.finrank (ZMod 2) (subspaceCommutator W.quotientRepresentation ⊤ B) ≤ 1 →
        rank B = 1) : rank A = 1 := by
  have hSdim := Submodule.isAtom_iff_finrank_eq_one.mp hS
  rcases offender_alternatives_of_critical_line ρ W D S hS hW hQ hA hcomm hdim with
    ⟨_, _, _, hstrong | ⟨_, he⟩⟩ | ⟨_, _, _, hstrong | ⟨_, he⟩⟩
  · exact (hstrongQ hstrong).elim
  · apply hlineW A hA
    rw [subrepresentation_commutator_dim, he, hSdim]
  · exact (hstrongW hstrong).elim
  · apply hlineQ A hA
    rw [he]
    exact (Submodule.finrank_map_le W.toSubmodule.mkQ S).trans hSdim.le

omit [Finite H] in
/-- The transvection-centralizer contradiction once rank one is obtained.
The two centralizer rigidity statements are intrinsic model inputs, while
`hcomm` and the larger actor are the critical-pair inputs of 13.8.23. -/
theorem no_rank_one_faithful_sections
    (W : Subrepresentation ρ) (S : Submodule (ZMod 2) U) (hS : IsAtom S)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A B : Subgroup H}
    (hA : IsElementaryTwo A) (hAB : A < B) (hrank : rank A = 1)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hcomm : ∀ b ∈ B, ∀ c ∈ fixedSpace ρ A, ρ b c - c ∈ S)
    (hcentW : ∀ E, IsElementaryTwo E → rank E = 1 →
      fixedCodim W.toRepresentation E = 1 →
      subspaceKernel W.toRepresentation (fixedSpace W.toRepresentation E) ⊤ = E)
    (hcentQ : ∀ E, IsElementaryTwo E → rank E = 1 →
      fixedCodim W.quotientRepresentation E = 1 →
      subspaceKernel W.quotientRepresentation (fixedSpace W.quotientRepresentation E) ⊤ = E) :
    False := by
  have hsmall : fixedCodim ρ A ≤ 2 := by omega
  obtain ⟨hcodW, hcodQ, _⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA.1 hsmall
  rcases faithful_sections_centralizer_sieve ρ W S hS hW hQ hA.1 hAB hsmall hcomm with
    ⟨_, _, hlt⟩ | ⟨_, _, hlt⟩
  · rw [hcentQ A hA hrank hcodQ] at hlt
    exact (lt_irrefl _ hlt)
  · rw [hcentW A hA hrank hcodW] at hlt
    exact (lt_irrefl _ hlt)
omit [Finite H] in
/-- A subspace whose codimension is too small cannot be centralized by
an actor with larger fixed codimension. In the G₂ argument this detects
noncommutation on the image of `C_Q_H(A₁)` in `Q_H/H_C`. -/
theorem exists_moved_vector_of_codimension_lt
    (D : Submodule (ZMod 2) U) (A : Subgroup H)
    (hsmall : Module.finrank (ZMod 2) (U ⧸ D) < fixedCodim ρ A) :
    ∃ a ∈ A, ∃ d ∈ D, ρ a d ≠ d := by
  classical
  by_contra hn
  have hfix : D ≤ fixedSpace ρ A := by
    intro d hd a
    by_contra hne
    exact hn ⟨a, a.property, d, hd, hne⟩
  have hm := Submodule.finrank_mono hfix
  have hd := D.finrank_quotient_add_finrank
  have hf := fixedCodim_add_finrank ρ A
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
