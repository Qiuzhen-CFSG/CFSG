module
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels
public import CFSG.Quasithin.ChapterB.InternalThompsonFixedSpace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedProjection

/-!
# The original fixed seed in the literal point action

The fixed-span argument provides an original moved vector fixed by the point
Sylow but not by the containing component. The conjugation action identifies
these conditions with the actual representation fixed spaces. Therefore the
vector survives the central quotient used in B.5.1.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A literal original fixed seed is nonzero modulo the component fixed space. -/
theorem source_a5_point_action_fixed_seed
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    letI := hr.normal; letI := hr.elementary
    ∃ z : Additive U, (((z.toMul : U) : H) : G) ∈ ⁅D.fullModule,L⁆ ∧
      z ∈ fixedSpace (action U) ((P.subgroupOf H).map (actionMk U)) ∧
      z ∉ fixedSpace (action U) ((I.subgroupOf H).map (actionMk U)) := by
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I
  let U := V.subgroupOf H
  let := hr.normal
  let := hr.elementary
  obtain ⟨z,hz,hzn⟩ := source_a5_point_fixed_seed_not_component_fixed D P I hLI hspan
  have hVI : V ≤ I := conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))
  have hzV : z ∈ V := hspan hz.1
  let w : Additive U := Additive.ofMul ⟨⟨z,(show I ≤ H from le_sup_left) (hVI hzV)⟩,hzV⟩
  refine ⟨w,hz.1,?_,?_⟩
  · apply (ChapterB.InternalThompsonAction.mem_fixedSpace_iff U (P.subgroupOf H) w).mpr
    intro p hp
    exact Subtype.ext (hz.2 p.val hp)
  · intro hw
    apply hzn
    have hc := (ChapterB.InternalThompsonAction.mem_fixedSpace_iff U (I.subgroupOf H) w).mp hw
    intro i hi
    exact congrArg H.subtype (hc ⟨i,(show I ≤ H from le_sup_left) hi⟩ hi)
end CFSG.Quasithin.Chapter10
