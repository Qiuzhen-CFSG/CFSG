module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Selection
public import Theory.SpecificGroups.AlternatingSix.SylowParabolicAction
public import Theory.GroupTheory.SylowOuterCover

/-!
# Constructing the A₆ head from the original parabolic

A₆ has a two-group of outer automorphisms, so its self-centralizing
normal copy together with a Sylow two-subgroup generates the ambient
actor. The original index-three parabolic therefore puts that actor
inside the natural S₆ automorphism subgroup. The complete binary S₆
catalogue restricts irreducibly to A₆, and the ratio-two degree estimate
forces the head to have dimension four. Intrinsic recognition supplies
its natural model, allowing the required change of component marking.

`StrictSource` applies this construction to the actual maximal quotient
of U_H/V₁. No invariant constituent or head model is an input.
Source: Aschbacher–Smith 13.8.21–26, printed pp.956–958,962,
using the actual binary models in G.5.1–2.
-/

public section
open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
variable {J : Type*} [Group J] [Finite J]

open Representation
open AlternatingSix.SylowParabolicAction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

omit [Finite J] in
/-- The actual S₆ catalogue makes the component restriction irreducible. -/
theorem component_irreducible_of_natural (C : Subgroup J) [C.Normal]
    (e : C ≃* A6) (hc : centralizer (C : Set J) = ⊥)
    (hn : (conjugationAction C e).range ≤ natural)
    (σ : Representation (ZMod 2) J E) [IsIrreducible σ] :
    IsIrreducible (σ.comp C.subtype) := by
  let a := conjugationAction C e
  let b : J →* natural := a.codRestrict natural (fun j => hn ⟨j, rfl⟩)
  let es : (Equiv.Perm (Fin 6)) ≃* natural := MonoidHom.ofInjective permutationAction_injective
  let f : J →* Equiv.Perm (Fin 6) := es.symm.toMonoidHom.comp b
  have he (j : J) : permutationAction (f j) = a j :=
    congrArg Subtype.val (es.apply_symm_apply (b j))
  have hf : Function.Injective f := by
    have ha : Function.Injective a := by
      apply (MonoidHom.ker_eq_bot_iff a).mp
      exact (conjugationAction_ker C e).trans hc
    intro x y h
    apply ha
    rw [← he, ← he, h]
  have hfC (c : C) : f c = (e c).val := by
    apply permutationAction_injective
    rw [he, permutationAction_coe]
    exact conjugationAction_on_inner C e c
  have hr : alternatingGroup (Fin 6) ≤ f.range := by
    intro c h
    obtain ⟨k, hk⟩ := e.surjective ⟨c, h⟩
    exact ⟨k.val, by rw [hfC, hk]⟩
  rcases extension_equiv_of_embedding f hf hr with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hsurj : Function.Surjective C.subtype := by
      intro j
      obtain ⟨c, hc⟩ := e.surjective (d j)
      refine ⟨c, d.injective ?_⟩
      apply Subtype.ext
      rw [hd]
      change f c.val = (d j).val
      rw [hfC, hc]
    exact (irreducible_comp_surjective_iff C.subtype hsurj σ).mpr inferInstance
  · let τ := σ.comp d.symm.toMonoidHom
    let : IsIrreducible τ :=
      (irreducible_comp_surjective_iff d.symm.toMonoidHom d.symm.surjective σ).mpr inferInstance
    have hi := BinaryAlternatingSix.alternatingModel_irreducible _
      (BinaryAlternatingSix.alternatingModel_of_symmetricModel τ (BinaryAlternatingSix.symmetric_classify τ))
    have heq : (τ.comp A6.subtype).comp e.toMonoidHom = σ.comp C.subtype := by
      apply MonoidHom.ext
      intro c
      change σ (d.symm (e c).val) = σ c
      congr 1
      apply d.injective
      rw [d.apply_symm_apply, hd, hfC]
    rw [← heq]
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr hi


open Theory.GroupTheory Representation.BinaryOffender

/-- Derive irreducibility of the component action from the original parabolic. -/
theorem component_irreducible_of_parabolic (C : Subgroup J)
    (hfit : C = generalizedFitting J) (e : C ≃* A6)
    (S : Sylow 2 J) (P : Subgroup J) (hSP : (S : Subgroup J) ≤ P)
    (hi : (S : Subgroup J).relIndex P = 3)
    (σ : Representation (ZMod 2) J E) [IsIrreducible σ] :
    IsIrreducible (σ.comp C.subtype) := by
  let : C.Normal := hfit ▸ inferInstance
  obtain ⟨_, hc⟩ := component_properties C hfit e
  have ho : IsPGroup 2 (MulAut.Outer C) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact inner_index)
  have hg : C ⊔ (S : Subgroup J) = ⊤ := by
    simpa only [hc, sup_bot_eq] using sup_centralizer_sup_sylow_eq_top C ho S
  exact component_irreducible_of_natural C e hc (parabolic_natural C e S P hSP hg hi) σ

/-- The ratio-two bound now constructs a natural model of the whole head. -/
theorem head_marked_of_parabolic (C : Subgroup J)
    (hfit : C = generalizedFitting J) (e : C ≃* A6)
    (S : Sylow 2 J) (P : Subgroup J) (hSP : (S : Subgroup J) ≤ P)
    (hi : (S : Subgroup J).relIndex P = 3)
    (σ : Representation (ZMod 2) J E) [IsIrreducible σ] (hf : Function.Injective σ)
    (A : Subgroup J) (hA : IsElementaryTwo A) (hb : fixedCodim σ A ≤ 2 * rank A) :
    ∃ (e' : C ≃* Alternating) (E' : E ≃ₗ[ZMod 2] Natural),
      ∀ c : C, ∀ v, E' (σ c v) = alternatingAction (e' c) (E' v) := by
  have hiC := component_irreducible_of_parabolic C hfit e S P hSP hi σ
  obtain ⟨e', E', f, _, hfC, he, _⟩ := marked_natural σ C hfit e hf hiC A hA hb
  refine ⟨e', E', fun c v => ?_⟩
  have hh := he c v
  rw [hfC] at hh
  exact hh


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
