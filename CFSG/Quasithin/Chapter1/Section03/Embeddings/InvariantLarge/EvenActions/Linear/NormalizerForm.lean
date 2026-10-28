module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.FieldGraph
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm

/-!
# Uniform normal forms for standard Cartan normalizer actors

Let B lie in the specified split torus of PSL₃ over a finite field of
characteristic two. A standard automorphism preserving B and the upper
unipotent subgroup acts on every element of B by the same field automorphism,
possibly followed on the input by the opposition graph automorphism.

First factor the actor using the three standard matrix compatibility laws.
The field and opposition factors preserve U, so the remaining GL₃ factor does
also. The proved Borel kernel fixes each transformed torus element because
its image lies back in B. This argument does not require graph stability of B;
the existing field–graph descent derives that stability from such an actor.

This completes the normalizer-form helper. The source assembly owner must
still supply the three compatibility laws from the standard-automorphism
calculation, as well as its separate Cartan alignment. Source:
Aschbacher–Smith, `refs/quasithin.pdf`, printed p.511 and A.3.15(5), printed
pp.50–51; GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.NormalizerForm
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private theorem preserves_left_factor {G : Type*} [Group G]
    (H : Subgroup G) (a b : MulAut G)
    (hab : H.map (a*b).toMonoidHom = H) (hb : H.map b.toMonoidHom = H) :
    H.map a.toMonoidHom = H := by
  have he : (a*b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := rfl
  rwa [he, ← Subgroup.map_map, hb] at hab

/-- Every standard actor preserving U and B has one uniform field or
field–opposition action on B. Only the three matrix compatibility laws are
retained as inputs; the linear Borel kernel is proved in the lower module. -/
theorem standard_normalizer_action
    (hfield : ∀ (σ : F ≃+* F) (m : GL (Fin 3) F),
      fieldAction F σ * linearConj F m =
        linearConj F (Matrix.GeneralLinearGroup.map σ.toRingHom m) * fieldAction F σ)
    (hgraph : ∀ m : GL (Fin 3) F, ∃ m' : GL (Fin 3) F,
      graph F * linearConj F m = linearConj F m' * graph F)
    (hcomm : ∀ σ : F ≃+* F, Commute (fieldAction F σ) (graph F))
    (B : Subgroup PSL(3,F)) (hB : B ≤ torus F)
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F)
    (hU : (unipotent F).map α.toMonoidHom = unipotent F)
    (hαB : B.map α.toMonoidHom = B) :
    ∃ σ : F ≃+* F,
      (∀ b ∈ B, α b = fieldAction F σ b) ∨
      (∀ b ∈ B, α b = fieldAction F σ (oppositionGraph F b)) := by
  obtain ⟨m,σ,h | h⟩ := standard_opposition_factorization F hfield hgraph hcomm α hα
  · refine ⟨σ, Or.inl ?_⟩
    have hm := preserves_left_factor (unipotent F) (linearConj F m) (fieldAction F σ)
      (by rwa [← h]) (fieldAction_unipotent F σ)
    intro b hb
    have hfb : fieldAction F σ b ∈ torus F :=
      hB ((field_preserves_subgroup F σ B hB).le (mem_map_of_mem _ hb))
    have hab : α b ∈ torus F := hB (hαB.le (mem_map_of_mem _ hb))
    rw [h] at hab ⊢
    exact linearConj_torus_kernel F m hm _ hfb hab
  · refine ⟨σ, Or.inr ?_⟩
    have hfg : (unipotent F).map (fieldAction F σ * oppositionGraph F).toMonoidHom =
        unipotent F := by
      change (unipotent F).map
        ((fieldAction F σ).toMonoidHom.comp (oppositionGraph F).toMonoidHom) = _
      rw [← Subgroup.map_map, oppositionGraph_unipotent, fieldAction_unipotent]
    have hm := preserves_left_factor (unipotent F) (linearConj F m)
      (fieldAction F σ * oppositionGraph F) (by simpa only [h, mul_assoc] using hU) hfg
    intro b hb
    have hgb : oppositionGraph F b ∈ torus F :=
      (oppositionGraph_torus F).le (mem_map_of_mem _ (hB hb))
    have hfgb : fieldAction F σ (oppositionGraph F b) ∈ torus F :=
      (field_preserves_subgroup F σ (torus F) le_rfl).le (mem_map_of_mem _ hgb)
    have hab : α b ∈ torus F := hB (hαB.le (mem_map_of_mem _ hb))
    rw [h] at hab ⊢
    exact linearConj_torus_kernel F m hm _ hfgb hab

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
