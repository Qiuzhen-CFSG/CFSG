module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Models
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components
public import Theory.GroupTheory.SolvableResidual

/-!
# The three surviving B.5 branches on the original reduced action

The actual component excludes the solvable S₃ actor. In the outer A₆--C₃
configuration every perfect subgroup lies in the A₆ factor: its image in
the cyclic outer quotient and then in the cubic product factor is trivial.
Component maximality would identify the source component with A₆, contrary
to its three-rank one. Thus the quasisimple, two-factor and hyperplane rows
are the only remaining B.5.6 alternatives, with all their module data intact.

This is the literal classification consumer on the original offender actor,
not yet the extraction of the four moved-module markings. Its Thompson
movement premise is the authorized earlier result owned by
`qt-d-1317-supplements`.
Source: Aschbacher--Smith 13.1.10, printed pp.871--872; B.5.6, printed p.105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
universe u v

private theorem perfect_le_outerFirst {D : Type*} [Group D] [Finite D]
    (d : ChapterB.OuterSixThreeShape D) (K : Subgroup D) [Group.IsPerfect K] :
    K ≤ d.first := by
  let C := d.first ⊔ d.second
  let : d.first.Normal := d.first_normal
  let : d.second.Normal := d.second_normal
  have hC : _root_.commutator D ≤ C :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top d.generates inferInstance
  have hKC : K ≤ C := by
    rw [← K.commutator_eq_self]
    exact (commutator_mono le_top le_top).trans hC
  let e := subgroupOfEquivOfLe hKC
  let : Group.IsPerfect (K.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f : C →* d.second := (MonoidHom.snd _ _).comp d.product.symm.toMonoidHom
  let r := f.comp (K.subgroupOf C).subtype
  have hc : IsMulCommutative d.second :=
    ⟨⟨fun x y => d.secondEquiv.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  let := hc
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hr : ∀ x, r x = 1 := by
    intro x
    have hs : Subsingleton r.range := by
      by_contra! h
      exact Group.IsPerfect.not_isMulCommutative r.range inferInstance
    exact congrArg Subtype.val (Subsingleton.elim (r.rangeRestrict x) 1)
  intro k hk
  let x : C := ⟨k,hKC hk⟩
  have he := congrArg Subtype.val (d.product.apply_symm_apply x)
  rw [d.product_apply] at he
  have hsecond : (d.product.symm x).2 = 1 := hr (⟨x,hk⟩ : K.subgroupOf C)
  rw [hsecond, coe_one, mul_one] at he
  change (x : D) ∈ d.first
  rw [← he]
  exact (d.product.symm x).1.property

private theorem no_outer_of_component_three_rank_one {D : Type*} [Group D] [Finite D]
    (d : ChapterB.OuterSixThreeShape D) {K : Subgroup D}
    (hK : IsComponent D K) (hr : primeRank 3 K = 1) : False := by
  let : Group.IsPerfect K := hK.2.toIsPerfect
  have he := hK.eq_of_le d.first_isComponent (perfect_le_outerFirst d K)
  have ht := d.first_three_rank
  rw [he] at hr
  omega

private theorem no_symmetricThree_of_component {D : Type*} [Group D]
    (e : D ≃* Equiv.Perm (Fin 3)) {K : Subgroup D} (hK : IsComponent D K) : False := by
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple K := hK.2
  let := IsQuasisimple.simple (G := K)
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

variable {G : Type u} [Group G] [Finite G]
/-- The S₃ and outer A₆ rows are excluded on the literal source actor. -/
theorem reducedOffender_three_cases
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    let ρ := (reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype
    (IsQuasisimple (generalizedFitting (offenderSubgroup (reducedRepresentation L))) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ
        (generalizedFitting (offenderSubgroup (reducedRepresentation L))))) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (HyperplaneCase ρ) := by
  have hc := reducedOffender_component h hmany hL hn hmove
  have hr : primeRank 3 ((NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L))) = 1 := by
    obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h hmany hL hn
    let e := (subgroupOfEquivOfLe (componentImage_le_reducedOffender h hL hn hmove)).trans
      (reducedImageEquivMovedImage h hmany hL hn)
    exact (prime_model_ranks hp hp3 (hm.of_mulEquiv e)).2
  cases reducedOffender_nontrivialAlternative h hmany hL hn hmove with
  | quasisimple hq actions => exact Or.inl ⟨hq,⟨actions⟩⟩
  | symmetricThree c => exact (no_symmetricThree_of_component c.equiv hc).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact (no_outer_of_component_three_rank_one c hc hr).elim
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
