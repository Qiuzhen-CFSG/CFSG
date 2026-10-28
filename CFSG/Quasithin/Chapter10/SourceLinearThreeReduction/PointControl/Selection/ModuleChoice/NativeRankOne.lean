module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.FullRows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.BinaryComponentRows

/-!
# The rank-one row on the original full action

The B.5.6 factor containing the original binary rank-one component cannot
be an SL₃ factor. Perfectness excludes the symmetric-three and symmetric-five
factors. Thus its literal image modulo the full orbit-fixed space is one
natural SL₂ module over a binary field of degree greater than one.

The full-action application retains the original component inclusion and
centralizer quotient. It requires a genuine binary rank-one isomorphism
for L/O₂(L); it does not assert the remaining component recognition, quiet
support, or the even-degree fixed-kernel stabilization.
Source: Aschbacher--Smith B.5.6(3), 3.2.6 and 10.1.1(1),
printed pp.105,581,741.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.QuasisimpleSource

/-- One natural rank-one row on the specified moved subspace and fixed quotient. -/
structure NaturalFactorRow {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) where
  space : Subrepresentation ρ
  field : BinaryField
  degree_gt_one : 1 < field.degree
  space_eq : space.toSubmodule = moved ρ A
  model : ActionEquiv
    (((fixed ρ).quotientImage space).toRepresentation.comp A.subtype) (linearNatural field 2)

private theorem rank_one_factor_natural
    {Q V F : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} [A.Normal]
    {U : Subrepresentation ρ} (hA : IsComponent Q A)
    (he : A ≃* SL(2,F)) (h : ChapterB.SourceInduction.SourceFactorCase ρ A U) :
    U.toSubmodule = moved ρ A ∧
      ∃ E : BinaryField, 1 < E.degree ∧
        IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) E 2 := by
  obtain ⟨hm, hn | hn⟩ := h.rankOne_of_binary_component hA le_rfl he
  · obtain ⟨E,⟨e⟩⟩ := hn
    refine ⟨hm,E,?_,⟨e⟩⟩
    by_contra hn
    have hd : E.degree = 1 := by have := E.degree_pos; omega
    let f : A ≃* Equiv.Perm (Fin 3) := e.groupEquiv.trans
      ((ChapterB.QuasisimpleSource.ExtensionConsequences.degreeOneNaturalEquiv E hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let := hA.2
    let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
      Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
    have hc := Group.IsPerfect.commutator_eq_top (G := Equiv.Perm (Fin 3))
    have hle := alternatingGroup.commutator_perm_le (α := Fin 3)
    rw [hc] at hle
    have ht : alternatingGroup (Fin 3) = ⊤ := top_unique hle
    have hs := ht.ge (show Equiv.swap (0 : Fin 3) 1 ∈ (⊤ : Subgroup (Equiv.Perm (Fin 3))) from mem_top _)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs
  · obtain ⟨e⟩ := hn
    exfalso
    let := hA.2
    let : Group.IsPerfect (Equiv.Perm (Fin 5)) :=
      Group.IsPerfect.ofSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
    have hc := Group.IsPerfect.commutator_eq_top (G := Equiv.Perm (Fin 5))
    have hle := alternatingGroup.commutator_perm_le (α := Fin 5)
    rw [hc] at hle
    have ht : alternatingGroup (Fin 5) = ⊤ := top_unique hle
    have hs := ht.ge (show Equiv.swap (0 : Fin 5) 1 ∈ (⊤ : Subgroup (Equiv.Perm (Fin 5))) from mem_top _)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
/-- The actual full-action factor belonging to a marked binary rank-one component. -/
theorem full_rank_one_factor
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    letI : U.Normal := (source_full_module_reduced D).normal
    letI : IsElementaryAbelian 2 U := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let Y := offenderSubgroup ρ
    let σ : Representation (ZMod 2) Y (Additive U) := ρ.comp Y.subtype
    let A : Subgroup Y := ((L.subgroupOf M).map q).subgroupOf Y
    Nonempty (NaturalFactorRow σ A) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let A := ((L.subgroupOf M).map q).subgroupOf Y
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hAX : L.subgroupOf M ≤ (localOrbit T L).subgroupOf M :=
    comap_mono (le_componentOrbit L T)
  have hAY : (L.subgroupOf M).map q ≤ Y :=
    (map_mono (f := q) hAX).trans (full_orbit_image_le_offender D hJ)
  have hA : IsComponent Y A := (full_action_component_pair D ht htn).1.subgroupOf hAY
  obtain ⟨a⟩ := full_action_original_component_equiv D hn
  let f : A ≃* SL(2,F) := (subgroupOfEquivOfLe hAY).trans (a.trans e)
  obtain ⟨d⟩ := full_module_two_factor_case D hn hJ
  have hex : ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype),
      d.first = A := by
    rcases full_module_factor_alignment D hna hJ ht htn d with ⟨ha,_⟩ | ⟨ha,_⟩
    · exact ⟨d,ha.symm⟩
    · let ds : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype) := {
        first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
      refine ⟨ds,?_⟩
      exact ha.symm
  obtain ⟨d,hd⟩ := hex
  let : d.first.Normal := d.product.swap.second_normal
  have hdA : IsComponent Y d.first := hd.symm ▸ hA
  obtain ⟨hm,E,hE,he⟩ := rank_one_factor_natural
    (ρ := ρ.comp Y.subtype) (A := d.first) (U := d.firstSpace) (F := F) hdA
    ((MulEquiv.subgroupCongr hd).trans f) d.firstCase
  obtain ⟨he⟩ := he
  have hr : Nonempty (NaturalFactorRow (ρ.comp Y.subtype) d.first) :=
    ⟨⟨d.firstSpace,E,hE,hm,he⟩⟩
  simpa only [hd] using hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
