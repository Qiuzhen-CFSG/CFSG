module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Transvections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.ModuleSieve

/-!
# The final module contradiction for the seven-point branch

For the actual subrepresentation `W` and its literal quotient, the monolith
and the nontrivial component actions imply faithfulness. A rank-one critical
actor with the source codimension bound acts with fixed codimension one on
both sections. Equivariant natural submodules then identify both pointwise
centralizers with the actor, contradicting the strict containment in
13.8.23(4). The second theorem derives rank one when the actor is a group of
transvections on either section.

The local source application must still produce the natural submodules,
the nontrivial component action on `W`, and the transvection alternative.
These are conditional module results, not an assertion of 13.8.24.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.22–24, printed pp.957–959 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)
  (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)

include hφ

/-- The centralizer contradiction once the source supplies rank one and
compatible natural submodules in the two actual sections. -/
theorem no_rank_one_critical_configuration
    (W : Subrepresentation ρ) (K A : Subgroup H)
    (hK : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hKQ : ∃ k ∈ K, ∃ q : U ⧸ W.toSubmodule, W.quotientRepresentation k q ≠ q)
    (hA : IsElementaryTwo A) (hrank : rank A = 1)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hW : HasNaturalSubmodule W.toRepresentation φ)
    (hQ : HasNaturalSubmodule W.quotientRepresentation φ)
    (hstrict : A < subspaceKernel W.toRepresentation (fixedSpace W.toRepresentation A) ⊤ ∨
      A < subspaceKernel W.quotientRepresentation (fixedSpace W.quotientRepresentation A) ⊤) :
    False := by
  obtain ⟨_, _, hw, hq, _, _⟩ :=
    rank_one_faithful_sections ρ W K A hK hKW hKQ hA.1 hrank hbound
  obtain ⟨jw, hjw, hew⟩ := hW
  obtain ⟨jq, hjq, heq⟩ := hQ
  rcases hstrict with hs | hs
  · exact (ne_of_lt hs)
      (pointwiseCentralizer_of_fixedCodim_one W.toRepresentation φ hφ jw hjw hew hA hw).symm
  · exact (ne_of_lt hs)
      (pointwiseCentralizer_of_fixedCodim_one W.quotientRepresentation φ hφ jq hjq heq hA hq).symm

/-- The last inference of the source proof, with all section constructions
literal and with the still-needed natural identifications explicit. -/
theorem exclude_of_transvection_section
    (W : Subrepresentation ρ) (K A : Subgroup H)
    (hK : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hKQ : ∃ k ∈ K, ∃ q : U ⧸ W.toSubmodule, W.quotientRepresentation k q ≠ q)
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hW : HasNaturalSubmodule W.toRepresentation φ)
    (hQ : HasNaturalSubmodule W.quotientRepresentation φ)
    (ht : (∀ a ∈ A, a ≠ 1 → fixedCodim W.toRepresentation (Subgroup.zpowers a) = 1) ∨
      (∀ a ∈ A, a ≠ 1 → fixedCodim W.quotientRepresentation (Subgroup.zpowers a) = 1))
    (h23 : rank A = 1 →
      A < subspaceKernel W.toRepresentation (fixedSpace W.toRepresentation A) ⊤ ∨
      A < subspaceKernel W.quotientRepresentation (fixedSpace W.quotientRepresentation A) ⊤) :
    False := by
  have hr : rank A = 1 := by
    rcases ht with ht | ht
    · obtain ⟨j, hj, he⟩ := hW
      exact rank_one_of_transvections W.toRepresentation φ hφ j hj he hA ht
    · obtain ⟨j, hj, he⟩ := hQ
      exact rank_one_of_transvections W.quotientRepresentation φ hφ j hj he hA ht
  exact no_rank_one_critical_configuration ρ φ hφ W K A hK hKW hKQ hA hr hbound
    hW hQ (h23 hr)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
