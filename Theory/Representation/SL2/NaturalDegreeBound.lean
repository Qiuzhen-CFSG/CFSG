module
public import Theory.Representation.SL2.NaturalSectionBudget
public import Theory.Representation.SL2.NaturalHomogeneous
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.ThreeCopies
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# The two-copy bound from a faithful natural actor

A natural constituent has invariant type under the full compatible normalizer.
Clifford theory therefore makes its normal-subgroup restriction semisimple and
isotypic. If its degree exceeded two natural copies, selection over the same
elementary actor would give three invariant natural sections. Each costs at
least the actor's rank, contradicting its two-rank fixed-codimension budget.

The actor is required to act faithfully on the marked SL₂ quotient; no
assumption on the order of the full normalizer quotient is made.
Source: Aschbacher--Smith D.3.9(1) and D.3.21(3), printed pp.199--200,205--206.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace Representation.SL2AutomorphismNatural
universe u v
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  {G : Type u} [Group G] [Finite G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The same faithful elementary actor bounds the total natural multiplicity by two. -/
theorem degree_le_two_of_faithful_actor
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (K : Subgroup G) [K.Normal]
    (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (α : G →* MulAut (SL(2,F)))
    (hα : ∀ (a : G) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hf : Function.Injective (α.comp A.subtype))
    (hb : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) (Fin 2 → F) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let : Nontrivial V := (inferInstance : IsSimpleModule (ZMod 2)[G] ρ.asModule).nontrivial
  have ht : (normalTypeAction ρ K).inertia I = ⊤ := by
    apply top_unique
    intro a _
    exact natural_sameModule_conjugate ρ K q α hα I E hE a
  have htype := restriction_isotypic_of_typeInertia_top ρ K I hI ht
  let H := K ⊔ A
  let B := K.subgroupOf H
  let P := A.subgroupOf H
  let e := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let eA := subgroupOfEquivOfLe (show A ≤ H from le_sup_right)
  let σ := ρ.comp H.subtype
  let I' := I.compActors e.toMonoidHom
  let q' := q.comp e.toMonoidHom
  let α' := α.comp H.subtype
  have hα' (a : H) (k : B) : q' (MulAut.conjNormal a k) = α' a (q' k) :=
    hα a.val (e k)
  let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ inferInstance K
  let : IsSemisimpleModule (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) :=
    comp_semisimple_of_surjective (ρ.comp K.subtype) e.toMonoidHom e.surjective
  have ht' : IsIsotypicOfType (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) I'.asSubmodule :=
    isotypic_comp_equiv (ρ.comp K.subtype) e I htype
  have hP : IsElementaryTwo P := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
    intro hp
    have hr := rank_subgroupOf (show A ≤ H from le_sup_right)
    change rank P = rank A at hr
    rw [hp,BinaryOffender.rank_bot] at hr
    have := hA.rank_pos
    omega
  have hf' : Function.Injective (α'.comp P.subtype) := by
    intro a b hab
    apply eA.injective
    exact hf hab
  have hb' : fixedCodim σ P ≤ 2 * rank P := by
    change fixedCodim (ρ.comp H.subtype) (A.subgroupOf H) ≤ 2 * rank (A.subgroupOf H)
    rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right),
      rank_subgroupOf (show A ≤ H from le_sup_right)]
    exact hb
  have hd := degree_le_two_of_section_rank_bound σ B ht' P hP
    (codisjoint_subgroupOf_sup K A).eq_top hb' ?_
  · have hdim : Module.finrank (ZMod 2) I'.asSubmodule = Module.finrank (ZMod 2) (Fin 2 → F) :=
      E.finrank_eq.symm
    simpa only [hdim] using hd
  · intro W _ _ τ X hX
    let er := equiv_of_asSubmodule_equiv (τ.comp B.subtype)
      ((ρ.comp K.subtype).comp e.toMonoidHom) (X.compActors B.subtype) I' hX.some
    let E' : (Fin 2 → F) ≃ₗ[ZMod 2] I'.toSubmodule := E
    have hE' (k : B) (v : Fin 2 → F) :
        E' ((q' k).val.mulVec v) = I'.toRepresentation k (E' v) := hE (e k) v
    let b : Representation.Equiv (X.compActors B.subtype).toRepresentation
        (SL2NaturalOffenders.NoStrong.natural.comp q') := {
      __ := er.toLinearEquiv.trans E'.symm
      isIntertwining' k := by
        apply LinearMap.ext
        intro v
        change E'.symm (er.toLinearEquiv ((X.compActors B.subtype).toRepresentation k v)) =
          (q' k).val.mulVec (E'.symm (er.toLinearEquiv v))
        apply E'.injective
        rw [E'.apply_symm_apply,hE',E'.apply_symm_apply]
        exact LinearMap.congr_fun (er.isIntertwining' k) v }
    exact SL2NaturalOffenders.rank_le_fixedCodim_of_natural_section X.toRepresentation B
      q' (hq.comp e.surjective) α' hα' b hF P hP hf'
end Representation.SL2AutomorphismNatural
