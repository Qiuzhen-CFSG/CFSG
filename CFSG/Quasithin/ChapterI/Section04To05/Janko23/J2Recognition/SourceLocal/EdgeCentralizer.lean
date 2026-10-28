module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.Systems
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Centralizers attached to an edge of the J₂ subgroup graph

A perfect group normalizing a cyclic subgroup centralizes it. Applied to
both order-three endpoints, this identifies an A₅ pointwise edge fixer
with the centralizer of the generated A₄. Every subgroup B of that fixer
therefore has both endpoints in the literal subgroup C_G(B).

These are the incidence and map conventions needed for Aschbacher,
*Sporadic Groups* (1994), 47.5 and the construction in 47.10, pp.263, 266.
The A₅ identification of the edge fixer remains an explicit earlier input.
-/

public section

open Subgroup
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem perfect_le_centralizer_of_cyclic
    (P A : Subgroup G) [Group.IsPerfect P] [IsCyclic A]
    (h : P ≤ normalizer (A : Set G)) : P ≤ centralizer (A : Set G) := by
  let _ := (IsCyclic.mulAutMulEquiv A).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv A).injective
  let f : P →* MulAut A := A.normalizerMonoidHom.comp (inclusion h)
  have hf := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hf
  intro p hp
  have he : A.normalizerMonoidHom (inclusion h ⟨p, hp⟩) = 1 := hf (mem_top _)
  have hk : inclusion h ⟨p, hp⟩ ∈ A.normalizerMonoidHom.ker := he
  rwa [normalizerMonoidHom_ker] at hk

theorem edgeFixer_eq_centralizer_join_of_perfect (D : Seed G) (A B : D.Vertex)
    [Group.IsPerfect (edgeFixer G A B)] :
    edgeFixer G A B = centralizer ((A.val ⊔ B.val : Subgroup G) : Set G) := by
  have hn : edgeFixer G A B = normalizer (A.val : Set G) ⊓
      normalizer (B.val : Set G) := by
    rw [edgeFixer, D.stabilizer_eq_normalizer, D.stabilizer_eq_normalizer]
  have hcyc (V : D.Vertex) : IsCyclic V.val :=
    isCyclic_of_prime_card (D.vertex_card V)
  let := hcyc A
  let := hcyc B
  apply le_antisymm
  · apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mp
      exact perfect_le_centralizer_of_cyclic _ _ (hn ▸ inf_le_left)
    · apply le_centralizer_iff.mp
      exact perfect_le_centralizer_of_cyclic _ _ (hn ▸ inf_le_right)
  · rw [hn]
    exact le_inf ((centralizer_le (show (A.val : Set G) ⊆ (A.val ⊔ B.val : Subgroup G)
        from show A.val ≤ A.val ⊔ B.val from le_sup_left)).trans (centralizer_le_normalizer _))
      ((centralizer_le (show (B.val : Set G) ⊆ (A.val ⊔ B.val : Subgroup G)
        from show B.val ≤ A.val ⊔ B.val from le_sup_right)).trans (centralizer_le_normalizer _))

theorem edgeFixer_eq_centralizer_join_of_alternatingFive (D : Seed G) (A B : D.Vertex)
    (h : Nonempty (edgeFixer G A B ≃* alternatingGroup (Fin 5))) :
    edgeFixer G A B = centralizer ((A.val ⊔ B.val : Subgroup G) : Set G) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (edgeFixer G A B) :=
    Group.IsPerfect.ofSurjective (f := h.some.symm.toMonoidHom) h.some.symm.surjective
  exact edgeFixer_eq_centralizer_join_of_perfect D A B

theorem join_le_centralizer_of_le_edgeFixer (D : Seed G) (A B : D.Vertex)
    (h : Nonempty (edgeFixer G A B ≃* alternatingGroup (Fin 5)))
    (T : Subgroup G) (hT : T ≤ edgeFixer G A B) :
    A.val ⊔ B.val ≤ centralizer (T : Set G) := by
  apply le_centralizer_iff.mp
  rw [edgeFixer_eq_centralizer_join_of_alternatingFive D A B h] at hT
  exact hT

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
