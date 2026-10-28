module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.QuasisimpleRows
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# The nonsplit natural three-space and its original fixed vectors

The actual section projection is a commutator-generated central cover.
The dual first-cohomology bound gives dimension four when its kernel is
nonzero. Simplicity rules out a fixed summand, so B.4.8(2) identifies the
Sylow-fixed space with the original central kernel. B.5.1(5) then supplies
a fixed supplement in the original module and extends that fixed-space
identity to every original vector fixed by the marked component Sylow.

Source: Aschbacher--Smith 13.1.10(4), pp.871--872; B.4.8(2), B.5.1(5),
and I.1.6(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
open Representation.OneCohomology
universe u

section NaturalExtension
variable {D V : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
  (s : MovedSection ρ K)
  (a : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3))

def threeCoverAction : Representation (ZMod 2) BinaryLinearThree.Group s.space.toSubmodule :=
  s.space.toRepresentation.comp (K.subtype.comp a.groupEquiv.symm.toMonoidHom)

/-- The marked cover uses the original component action on the original moved space. -/
theorem threeCoverAction_apply (g : BinaryLinearThree.Group) (v : s.space.toSubmodule) :
    threeCoverAction s a g v = s.space.toRepresentation (a.groupEquiv.symm g) v := by
  rfl

def threeCoverProjection : (threeCoverAction s a).IntertwiningMap BinaryLinearThree.W :=
  (a.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g v
      let g' : Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier := g
      have hh := a.intertwines (a.groupEquiv.symm g') (s.central.toSubmodule.mkQ v)
      exact hh.trans (congrArg
        (fun k => linearNatural BinaryField.two 3 k (a.linearEquiv (s.central.toSubmodule.mkQ v)))
        (a.groupEquiv.apply_symm_apply g')))

theorem threeCoverProjection_kernel :
    (threeCoverProjection s a).toLinearMap.ker = s.central.toSubmodule := by
  ext v
  change a.linearEquiv (s.central.toSubmodule.mkQ v) = 0 ↔ v ∈ s.central.toSubmodule
  rw [a.linearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem threeCoverProjection_isCover (hi : IsIrrPlus ρ K s.space.toSubmodule) :
    IsCover (threeCoverProjection s a) := by
  refine ⟨a.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
  · rw [threeCoverProjection_kernel]
    intro v hv g
    rw [s.central_eq] at hv
    exact hv (a.groupEquiv.symm g)
  · let τ := threeCoverAction s a
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      refine ⟨τ (a.groupEquiv ⟨g,hg⟩) ⟨v,hv⟩ - ⟨v,hv⟩,
        Coinvariants.sub_mem_ker _ _, ?_⟩
      change ρ (a.groupEquiv.symm (a.groupEquiv ⟨g,hg⟩)) v - v = ρ g v - v
      rw [a.groupEquiv.symm_apply_apply]
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

include a in
/-- I.1.6(4) bounds the actual fixed kernel; a nonzero kernel forces rank four. -/
theorem threeCover_dimension_four [FiniteDimensional (ZMod 2) V]
    (hi : IsIrrPlus ρ K s.space.toSubmodule) (hz : s.central.toSubmodule ≠ ⊥) :
    Module.finrank (ZMod 2) s.space.toSubmodule = 4 := by
  let p := threeCoverProjection s a
  have hk := finrank_ker_le_H1_of_cover p (threeCoverProjection_isCover s a hi)
  rw [SLThreeCentralExtension.finrank_H1_dual, threeCoverProjection_kernel] at hk
  have hp : 0 < Module.finrank (ZMod 2) s.central.toSubmodule := by
    let : Nontrivial s.central.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hz
    exact Module.finrank_pos
  have hd := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (threeCoverProjection_isCover s a hi).1,
    finrank_top, Module.finrank_fin_fun, threeCoverProjection_kernel] at hd
  omega

/-- The original cover has no fixed direct summand. -/
theorem threeCover_indecomposable (hi : IsIrrPlus ρ K s.space.toSubmodule) :
    ∀ A B : Submodule (ZMod 2) s.space.toSubmodule,
      (∀ g v, v ∈ A → threeCoverAction s a g v ∈ A) →
      (∀ g v, v ∈ B → threeCoverAction s a g v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥ := by
  apply indecomposable_of_cover_of_simple (threeCoverProjection s a)
    (threeCoverProjection_isCover s a hi)
  intro A hA
  by_cases hb : A = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff A).mp hb
    apply top_unique
    intro y _
    by_cases hy : y = 0
    · exact hy ▸ A.zero_mem
    obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero x y hx0 hy
    exact hg ▸ hA g x hx

/-- Relabeling the component leaves the literal central subspace unchanged. -/
theorem threeCover_fixed_eq_central :
    (threeCoverAction s a).invariants = s.central.toSubmodule := by
  rw [s.central_eq]
  ext v
  constructor
  · intro hv g
    have hh := hv (a.groupEquiv g)
    change s.space.toRepresentation (a.groupEquiv.symm (a.groupEquiv g)) v = v at hh
    rwa [a.groupEquiv.symm_apply_apply] at hh
  · intro hv g
    exact hv (a.groupEquiv.symm g)

/-- B.4.8(2) on the marked original moved section: the Sylow-fixed subspace
is exactly the component-fixed kernel, rather than an arbitrary line. -/
theorem threeCover_sylow_fixed [FiniteDimensional (ZMod 2) V]
    (hi : IsIrrPlus ρ K s.space.toSubmodule) (hz : s.central.toSubmodule ≠ ⊥)
    (S : Sylow 2 BinaryLinearThree.Group) :
    fixedSpace (threeCoverAction s a) (S : Subgroup BinaryLinearThree.Group) =
      (threeCoverAction s a).invariants :=
  ChapterB.NaturalExtensions.central_quotient_sylow (threeCoverAction s a)
    (threeCoverProjection s a) (threeCoverProjection_isCover s a hi).1
    (threeCoverProjection_isCover s a hi).2.1 (threeCover_indecomposable s a hi)
    (threeCover_dimension_four s a hi hz) S

end NaturalExtension

variable {G : Type u} [Group G] [Finite G]

/-- The nonsplit linear-three section has rank four on the literal U.
The original omega-center clause is proved separately in `IrreducibleMarkings`. -/
theorem singleThree_central_rank_four
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hi : IsIrrPlus
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) s.space.toSubmodule)
    (hz : s.central.toSubmodule ≠ ⊥)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype)
      (linearNatural BinaryField.two 3)) : rank (normalizerMoved L) = 4 := by
  have hd := threeCover_dimension_four s a hi hz
  have hj := componentImage_le_reducedOffender h hL hn hmove
  have he : s.space.toSubmodule =
      moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L) := by
    rw [s.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hj]
  rw [he, ← movedCoordinates_rank] at hd
  exact hd

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
section Supplement
variable {D V : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {K : Subgroup D}

omit [FiniteDimensional (ZMod 2) V] in
/-- Clause (5) of the genuine B.5.1 conclusion forces the original supplement
when the natural three-space has a nonzero lower central attachment. -/
theorem three_source_supplement
    (d : ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (a : ActionEquiv (d.sectionData.action.comp K.subtype) (linearNatural BinaryField.two 3))
    (hz : d.sectionData.central.toSubmodule ≠ ⊥) :
    d.sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  rcases d.clause_five with hs | ⟨_,_,hb⟩
  · exact hs
  · have he := hb ⟨a.groupEquiv.trans
        (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩
    exfalso
    apply hz
    rw [d.sectionData.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact he.le ⟨v.property,fun k => congrArg Subtype.val (hv k)⟩

/-- A vector fixed by a Sylow of the marked component is fixed by the whole
component when the original module is the moved space plus fixed vectors.
This is the fixed-vector step needed for the source omega-center. -/
theorem three_source_fixed_of_sylow
    (d : ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hi : IsIrrPlus ρ K d.sectionData.space.toSubmodule)
    (a : ActionEquiv (d.sectionData.action.comp K.subtype) (linearNatural BinaryField.two 3))
    (hz : d.sectionData.central.toSubmodule ≠ ⊥)
    (S : Sylow 2 BinaryLinearThree.Group) (v : V)
    (hv : ∀ g : S, ρ (a.groupEquiv.symm (g : BinaryLinearThree.Group)) v = v) : v ∈ fixedSpace ρ K := by
  have hs : v ∈ d.sectionData.space.toSubmodule ⊔ ρ.invariants :=
    three_source_supplement d a hz ▸ Submodule.mem_top
  obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp hs
  have hwS : (⟨w,hw⟩ : d.sectionData.space.toSubmodule) ∈
      fixedSpace (threeCoverAction d.sectionData a) (S : Subgroup BinaryLinearThree.Group) := by
    intro g
    apply Subtype.ext
    have hh := hv g
    rw [map_add, hc (a.groupEquiv.symm (g : BinaryLinearThree.Group))] at hh
    exact add_right_cancel hh
  rw [threeCover_sylow_fixed d.sectionData a hi hz S,
    threeCover_fixed_eq_central, d.sectionData.central_eq] at hwS
  intro k
  change ρ (k : D) (w + c) = w + c
  rw [map_add, hc]
  exact congrArg (fun x => x + c) (congrArg Subtype.val (hwS k))
end Supplement
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
