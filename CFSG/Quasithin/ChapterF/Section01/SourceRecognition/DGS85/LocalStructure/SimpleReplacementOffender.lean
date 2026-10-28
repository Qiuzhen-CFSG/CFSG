module
public import Theory.Representation.SimpleQuotientActionImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SimpleClosureQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementSection
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# The surviving replacement offender on a simple local quotient

Take the residual-moving simple section of the literal V=<Z_delta^X>.
For a simple enlarged quotient, the actual restricted quotient map has
kernel O₂(X)=X intersect Q_lambda. The section kills this kernel; its
vanishing fixed space makes its faithful action image the same quotient.
Thus the original escaping maximum abelian actor survives with precisely
its original index, not just an upper bound for its image order.

The output retains the original actor, section numerator and denominator,
the quotient representatives and the unchanged section vectors. The square
bound for Suzuki and projective-unitary actions consumes this offender in
NoncentralSimpleExclusion. It does not assert the Sylow conclusion of 6.4
or address a nonsimple quotient. Both neighboring-center branches are included.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, using the
quadratic bounds of corrected 5.12, pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
universe u v
variable {G : Type u} {D : Type v} [Group G] [Group D] [IsSimpleGroup D]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A simple enlarged quotient receives the actual nontrivial replacement offender and its sharp index bound. -/
theorem source_simple_replacement_offender_of_inter_normal (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* D) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (σ : Representation (ZMod 2) D W), Function.Injective σ ∧ fixedSpace σ ⊤ = ⊥ ∧
      ∃ f : X →* D, Function.Surjective f ∧ f.ker = pCore 2 X ∧
        f.ker = ((P (other i)).pCoreIn 2).subgroupOf X ∧
        (∀ x : X, ∃ y : localEnlargement d, (y : G) = (x : G) ∧ f x = q y) ∧
        ∃ U C : Subgroup G, U ≤ V ∧ Nonempty (BinaryConjugationSection X U C (σ.comp f)) ∧
        ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
          ¬ A ≤ (P (other i)).pCoreIn 2 ∧
          IsPGroup 2 ((A.subgroupOf X).map f) ∧
          IsQuadratic σ ((A.subgroupOf X).map f) ∧
          1 < Nat.card ((A.subgroupOf X).map f) ∧
          Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf X).map f)) ≤
            Nat.card ((A.subgroupOf X).map f) := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  obtain ⟨f,hf,hfk,hfj,hrep⟩ := source_simple_closure_quotient h hB i d hn q hq hk
  obtain ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,_,hcore,hfaith,_,hres,_,A,hA,hout,_,hquad,hbound⟩ :=
    source_replacement_simple_quadratic_section_of_inter_normal h hB hS i hn
  let := hW
  let := hWM
  let := hWf
  let : IsIrreducible ρ := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have himfix : fixedSpace (imageRepresentation ρ) ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone _ le_top).trans hres.le)
  have hρfix : fixedSpace ρ ⊤ = ⊥ := by
    have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ :=
      MonoidHom.ext (imageRepresentation_actionHom ρ)
    rw [←he,fixedSpace_comp_map,map_top_of_surjective (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective]
    exact himfix
  obtain ⟨_,e,he⟩ := actionImage_equiv_of_simple_quotient ρ f hf (hfk ▸ hcore) hρfix
  let σ := (imageRepresentation ρ).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hfaith.comp e.symm.injective
  have hσf (x : X) : σ (f x) = ρ x := by
    change imageRepresentation ρ (e.symm (f x)) = ρ x
    rw [←he,e.symm_apply_apply,imageRepresentation_actionHom]
  have hcomp : σ.comp f = ρ := MonoidHom.ext hσf
  have hσfix : fixedSpace σ ⊤ = ⊥ := by
    rw [fixedSpace_comp_map,map_top_of_surjective _ e.symm.surjective]
    exact himfix
  have hAX : A ≤ X := hA.1.trans (le_conjugateSpanBy _ _)
  have hc : Nat.card ((A.subgroupOf X).map f) = ((P (other i)).pCoreIn 2).relIndex A :=
    actor_image_card_eq_relIndex X _ A f hfj hAX
  have hAe : (A.subgroupOf X).map f =
      ((A.subgroupOf X).map (actionHom ρ)).map e.toMonoidHom := by
    rw [map_map]
    exact congrArg (Subgroup.map · (A.subgroupOf X)) (MonoidHom.ext he).symm
  have hfix : fixedSpace σ ((A.subgroupOf X).map f) =
      fixedSpace (imageRepresentation ρ) ((A.subgroupOf X).map (actionHom ρ)) := by
    rw [hAe,fixedSpace_comp_map,map_map]
    have heid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by ext a; simp
    rw [heid,map_id]
  refine ⟨W,hW,hWM,hWf,σ,hσ,hσfix,f,hf,hfk,hfj,hrep,U,C,hUV,⟨hcomp.symm ▸ s⟩,
    A,hA,hout,((isPGroup_pCoreIn 2 _).to_le hA.1).comap_subtype.map f,?_,?_,?_⟩
  · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ w
    simpa only [hσf,imageRepresentation_actionHom] using
      hquad (actionHom ρ x) (mem_map_of_mem _ hx) (actionHom ρ y) (mem_map_of_mem _ hy) w
  · rw [hc]
    have hn1 : ((P (other i)).pCoreIn 2).relIndex A ≠ 1 :=
      fun he => hout (relIndex_eq_one.mp he)
    let := d.finite_P
    let : Finite X := Finite.of_injective (inclusion (conjugateSpanBy_le_self
      ((source_core_le_borel (Classical.choice (h.local_data i))).trans
        (le_sup_right.trans d.supplement.le)))) (inclusion_injective _)
    let : Finite A := Finite.of_injective (inclusion hAX) (inclusion_injective _)
    have hp : 0 < ((P (other i)).pCoreIn 2).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
    omega
  · rw [hfix,hc]
    exact hbound

/-- The original noncentral interface, retained as a specialization of the general construction. -/
theorem source_simple_replacement_offender (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G))
    (q : localEnlargement d →* D) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (σ : Representation (ZMod 2) D W), Function.Injective σ ∧ fixedSpace σ ⊤ = ⊥ ∧
      ∃ f : X →* D, Function.Surjective f ∧ f.ker = pCore 2 X ∧
        f.ker = ((P (other i)).pCoreIn 2).subgroupOf X ∧
        (∀ x : X, ∃ y : localEnlargement d, (y : G) = (x : G) ∧ f x = q y) ∧
        ∃ U C : Subgroup G, U ≤ V ∧ Nonempty (BinaryConjugationSection X U C (σ.comp f)) ∧
        ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
          ¬ A ≤ (P (other i)).pCoreIn 2 ∧
          IsPGroup 2 ((A.subgroupOf X).map f) ∧
          IsQuadratic σ ((A.subgroupOf X).map f) ∧
          1 < Nat.card ((A.subgroupOf X).map f) ∧
          Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf X).map f)) ≤
            Nat.card ((A.subgroupOf X).map f) := by
  have _ := hnc
  exact source_simple_replacement_offender_of_inter_normal h hB hS i d hn q hq hk

end CFSG.Quasithin.ChapterF.Source.DGS85
