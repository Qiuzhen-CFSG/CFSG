module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.FullRows

/-!
# Original moved-subgroup coordinates from the full fixed quotient

The image of L in the faithful full action is the original L/O₂(L), through
its literal inclusion and quotient map. A subrepresentation equal to that
component's moved space therefore gives coordinates on [V,L]. Its kernel
is exactly C_[V,L](L): the opposite component fixes [V,L], so fixation by
L is equivalent to fixation by the whole component orbit on this subgroup.

This bridge keeps the entire central kernel, and is independent of which
natural model is later recognized on the quotient image. Its actual consumer
is the rank-one recognition in RankOneRecognition.
Source: Aschbacher--Smith B.5.6(3), 3.2.6(3a) and 10.1.1(1),(3),
printed pp.105,581,741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The specified full-action quotient image marked on the original moved subgroup. -/
def HasMovedQuotientSection {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) Q V) (A : Subgroup Q) (P : Subrepresentation σ) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* A,
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((((fixed σ).quotientImage P).toRepresentation.comp A.subtype).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

set_option backward.isDefEq.respectTransparency false in
/-- The literal full-action moved image supplies the original conjugation section. -/
theorem full_moved_quotient_section
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    letI : U.Normal := (source_full_module_reduced D).normal
    letI : IsElementaryAbelian 2 U := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let Y := offenderSubgroup ρ
    let σ : Representation (ZMod 2) Y (Additive U) := ρ.comp Y.subtype
    let A : Subgroup Y := ((L.subgroupOf M).map q).subgroupOf Y
    ∀ P : Subrepresentation σ, P.toSubmodule = moved σ A →
      HasMovedQuotientSection D σ A P := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let σ : Representation (ZMod 2) Y (Additive U) := ρ.comp Y.subtype
  let A₀ := L.subgroupOf M
  let A := (A₀.map q).subgroupOf Y
  let W := ⁅D.fullModule,L⁆
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (hLM.trans D.maximalLocal_normalizes_fullModule)
  have hWM : W ≤ M := hWV.trans hVM
  have hAX : A₀ ≤ (localOrbit T L).subgroupOf M := comap_mono (le_componentOrbit L T)
  have hAY : A₀.map q ≤ Y := (map_mono hAX).trans (full_orbit_image_le_offender D hJ)
  let a : L ≃* A₀ := (subgroupOfEquivOfLe hLM).symm
  let f : L →* A := (subgroupOfEquivOfLe hAY).symm.toMonoidHom.comp
    ((q.subgroupMap A₀).comp a.toMonoidHom)
  have hf : Function.Surjective f := (subgroupOfEquivOfLe hAY).symm.surjective.comp
    ((q.subgroupMap_surjective A₀).comp a.surjective)
  have hk : pCore 2 L ≤ f.ker := by
    intro l hl
    apply Subtype.ext
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    exact Subtype.ext (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hl) v hv)
  let fbar := QuotientGroup.lift (pCore 2 L) f hk
  have hbar : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective _ _ hf hk
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hA : IsComponent Y A := (full_action_component_pair D ht htn).1.subgroupOf hAY
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot _).mpr hA.isCComponent.ne_bot
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  have hi : Function.Injective fbar := by
    apply fbar.ker_eq_bot_iff.mp
    rcases fbar.normal_ker.eq_bot_or_eq_top with hb | hh
    · exact hb
    exfalso
    obtain ⟨y,hy⟩ := exists_ne (1 : A)
    obtain ⟨x,rfl⟩ := hbar y
    exact hy (show x ∈ fbar.ker from hh ▸ mem_top _)
  let e := MulEquiv.ofBijective fbar ⟨hi,hbar⟩
  have he (l : L) : e (QuotientGroup.mk' (pCore 2 L) l) = f l := rfl
  intro P hP
  have hcomm : ⁅U,A₀⁆ = W.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVM,map_subgroupOf_eq_of_le hLM,
      map_subgroupOf_eq_of_le hWM]
  have hmem (v : Additive U) : v ∈ P.toSubmodule ↔ ((v.toMul : M) : G) ∈ W := by
    rw [hP]
    change v ∈ subspaceCommutator (ρ.comp Y.subtype) ⊤ A ↔ _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAY]
    change v ∈ subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (A₀.map q) ↔ _
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A₀]
    change (v.toMul : M) ∈ ⁅U,A₀⁆ ↔ _
    rw [hcomm]
    rfl
  have hinv (v : Additive U) : v ∈ σ.invariants ↔
      ((v.toMul : M) : G) ∈ centralizer (localOrbit T L : Set G) := by
    change v ∈ fixedSpace ρ Y ↔ _
    have hY : Y = ((localOrbit T L).subgroupOf M).map q :=
      full_offender_eq_orbit_image D hn hna hJ
    rw [hY]
    change v ∈ fixedSpace (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
        (((localOrbit T L).subgroupOf M).map q) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image]
    constructor
    · intro hv x hx
      exact congrArg M.subtype (hv ⟨x,(localOrbit T L).le_normalizer hx⟩ hx)
    · intro hv x hx
      exact Subtype.ext (hv x hx)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht htn
  have hfix (w : W) : (w : G) ∈ centralizer (localOrbit T L : Set G) ↔
      (w : G) ∈ centralizer (L : Set G) := by
    constructor
    · exact fun hw => centralizer_le (le_componentOrbit L T) hw
    · intro hw
      have hc : localOrbit T L ≤ centralizer ({(w : G)} : Set G) := by
        rw [hpair]
        apply sup_le
        · exact fun l hl => mem_centralizer_singleton_iff.mpr (hw l hl)
        · exact fun l hl => mem_centralizer_singleton_iff.mpr
            (full_moved_centralizes_partner D hJ ht htn w.property l hl)
      exact fun l hl => mem_centralizer_singleton_iff.mp (hc hl)
  let v (w : W) : Additive U := Additive.ofMul ⟨⟨w,hWM w.property⟩,hWV w.property⟩
  let Q := (fixed σ).quotientImage P
  let c : W →* Multiplicative Q.toSubmodule := {
    toFun := fun w => Multiplicative.ofAdd ⟨σ.invariants.mkQ (v w),
      ⟨v w,(hmem (v w)).mpr w.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_zero σ.invariants.mkQ
    map_mul' := by intro x y; apply Subtype.ext; exact map_add σ.invariants.mkQ (v x) (v y) }
  have hc : Function.Surjective c := by
    intro x
    obtain ⟨u,hu,hux⟩ := x.toAdd.property
    refine ⟨⟨u.toMul,(hmem u).mp hu⟩,?_⟩
    apply Subtype.ext
    exact hux
  refine ⟨e,⟨{
    section_le := source_full_moved_le_component D
    kernel_le := inf_le_left
    normalized := normalizer_commutator_ge_right _ _
    coordinates := c
    onto := hc
    kernel_eq := ?_
    equivariant := ?_ }⟩⟩
  · ext w
    change c w = 1 ↔ (w : G) ∈ sourceMovedFixed D
    have hh : c w = 1 ↔ σ.invariants.mkQ (v w) = 0 := Subtype.val_inj.symm
    have hz : σ.invariants.mkQ (v w) = 0 ↔ v w ∈ σ.invariants :=
      Submodule.Quotient.mk_eq_zero σ.invariants
    rw [hh,hz,hinv]
    change (w : G) ∈ centralizer (localOrbit T L : Set G) ↔ _
    rw [hfix]
    exact ⟨fun hw => ⟨w.property,hw⟩,fun hw => hw.2⟩
  · intro l w
    apply Subtype.ext
    change σ.invariants.mkQ (v _) = σ.invariants.mkQ (σ ((f l : A) : Y) (v w))
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change _ = ((ρ (q (a l : A₀)) (v w)).toMul : M)
    rw [ChapterB.InternalThompsonAction.action_apply]
    rfl

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
