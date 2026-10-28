module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.Held.LocalGeneration

/-!
# The Held generating-family assembly step

For the maximal subgroup of order 21504 (or its extension of order 43008),
a second Sylow overgroup with order divisible by nine suffices for
generation. Once both intrinsic rank-one E-generation bounds have been
proved, the two-element family is the input to E.1.12.

These are conditional assembly lemmas, not E.1.14(4). In particular this
module does not yet construct the local subgroups in the concrete Held
model or its outer extension, or prove their E-generation bounds. All
those obligations remain explicit. No older ambient-tau convention is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.12 and E.1.14(4), printed p.214, citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.9.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- The explicit pair is a generating family of Sylow overgroups. The
intrinsic E-generation bounds must be supplied by local proofs. -/
theorem held_pair_rankOne_generatingFamily (T : Sylow 2 G) (P B : Subgroup G)
    (hP : IsCoatom P) (hcard : Nat.card P = 21504 ∨ Nat.card P = 43008)
    (hB : 9 ∣ Nat.card B)
    (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hgenP : IsEGenerated 1 P) (hgenB : IsEGenerated 1 B) :
    sSup ({P, B} : Set (Subgroup G)) = ⊤ ∧
      ∀ H ∈ ({P, B} : Set (Subgroup G)),
        (T : Subgroup G) ≤ H ∧ IsEGenerated 1 H := by
  refine ⟨?_, ?_⟩
  · simpa only [sSup_insert, sSup_singleton] using Held.local_pair_sup_eq_top P B hP hcard hB
  · intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact ⟨hTP, hgenP⟩
    · obtain rfl := Set.mem_singleton_iff.mp hH
      exact ⟨hTB, hgenB⟩

end CFSG.Quasithin.ChapterE
