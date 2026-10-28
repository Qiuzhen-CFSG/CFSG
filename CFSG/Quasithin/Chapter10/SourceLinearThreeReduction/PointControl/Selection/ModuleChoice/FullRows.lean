module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.MovingSupport
public import Theory.GroupTheory.CComponent.QuasisimpleImage

/-!
# The full-module B.5 rows on the original component orbit

Local Thompson movement gives L₀ = [L₀,J(T)]. Its image therefore lies in
the offender subgroup of the literal full action M/C_M(V). The original
component pair survives in this quotient, and full commutator generation
excludes the hyperplane alternative of B.5.6. In the non-A₅ branch each
original component equals one source factor, identifying the offender
subgroup with the actual image of L₀.

The same factor decomposition separates the full moved subgroups directly,
without full/local equality or a minimality assumption. The positive full
fixed-layer branch supplies the local Thompson movement from 3.1.8.
These results retain every source quotient and inclusion; they do not yet
recognize the natural coordinates or identify the full and local modules.

Source: Aschbacher--Smith B.5.6, 3.2.2(3),(6), 3.2.6 and 10.1.1--2,
printed pp.105,579,581,741--742.
-/

@[expose] public noncomputable section
open Stellmacher Representation Representation.BinaryOffender
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The full M-action retains the original component and its conjugate. -/
theorem full_action_component_pair
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let A := L.subgroupOf M
    let tM : M := ⟨t, le_normalizer_componentOrbit L T ht⟩
    let B := A.map (MulAut.conj tM).toMonoidHom
    IsComponent (M ⧸ centralizer (U : Set M)) (A.map q) ∧
      IsComponent (M ⧸ centralizer (U : Set M)) (B.map q) ∧ A.map q ≠ B.map q := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let A := L.subgroupOf M
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let B := A.map (MulAut.conj tM).toMonoidHom
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let a : A ≃* L := subgroupOfEquivOfLe hLM
  have hcore : A.pCoreIn 2 ≤ q.ker := by
    rintro _ ⟨x,hx,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    have hxL : a x ∈ pCore 2 L := by
      rw [←pCore_map_iso 2 a]
      exact mem_map_of_mem _ hx
    have hc := source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hxL)
    intro v hv
    exact Subtype.ext (hc v hv)
  have hneA : A.map q ≠ ⊥ := by
    intro he
    have hAC : L ≤ centralizer (D.fullModule : Set G) := by
      intro l hl v hv
      have hh : q ⟨l,hLM hl⟩ = 1 := he.le (mem_map_of_mem q hl)
      have hc := (QuotientGroup.eq_one_iff _).mp hh
      exact congrArg M.subtype (hc ⟨v,hVM hv⟩ hv)
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAC))
  let := D.quasisimple
  have hAq : IsComponent (M ⧸ centralizer (U : Set M)) (A.map q) :=
    D.component_in_maximalLocal.isComponent_map_of_twoCore_killed
      (IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm)
      q (QuotientGroup.mk'_surjective _) hcore hneA
  have hBq : B.map q = (A.map q).map (MulAut.conj (q tM)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  refine ⟨hAq,hBq.symm ▸ hAq.map_equiv (MulAut.conj (q tM)),?_⟩
  let H := localJoin T L
  let V := D.moduleSubgroup.subgroupOf H
  let : V.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let p := QuotientGroup.mk' (centralizer (V : Set H))
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let A' := L.subgroupOf H
  let B' := A'.map (MulAut.conj tH).toMonoidHom
  have hHM : H ≤ M := sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  have hfull : D.moduleSubgroup ≤ D.fullModule := le_componentOrbit _ _
  have hk {x y : H} (he : q (inclusion hHM x) = q (inclusion hHM y)) : p x = p y := by
    apply (mul_inv_eq_one.mp)
    rw [←map_inv,←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc : inclusion hHM (x*y⁻¹) ∈ centralizer (U : Set M) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (inclusion hHM x * (inclusion hHM y)⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    intro v hv
    exact Subtype.ext (congrArg M.subtype (hc ⟨v,hHM v.property⟩ (hfull hv)))
  have hmapA : A'.map (inclusion hHM) = A := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx
      exact ⟨⟨x,(le_componentOrbit L T).trans le_sup_left hx⟩,hx,rfl⟩
  have hmapB : B'.map (inclusion hHM) = B := by
    rw [map_map,show (inclusion hHM).comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj tM).toMonoidHom.comp (inclusion hHM) from rfl,←map_map,hmapA]
  have reflect (C E : Subgroup H) (he : C.map (q.comp (inclusion hHM)) ≤
      E.map (q.comp (inclusion hHM))) : C.map p ≤ E.map p := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hyx⟩ := he (mem_map_of_mem (q.comp (inclusion hHM)) hx)
    exact ⟨y,hy,hk hyx⟩
  intro he
  change A.map q = B.map q at he
  apply (local_action_component_pair D ht htn).2.2
  apply le_antisymm (reflect A' B' ?_) (reflect B' A' ?_)
  · rw [←map_map,←map_map,hmapA,hmapB]
    exact he.le
  · rw [←map_map,←map_map,hmapA,hmapB]
    exact he.ge


/-- The original component orbit lies in the full action's offender subgroup
whenever the local Thompson subgroup moves the local module. -/
theorem full_orbit_image_le_offender
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ((localOrbit T L).subgroupOf M).map q ≤ offenderSubgroup ρ := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (localOrbit T L).subgroupOf M
  let S := D.ambientSylow
  let J := elementaryAbelianMaxJ (S : Subgroup M)
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  have hJmap : J.map M.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le
      (le_normalizer_componentOrbit L T))
  have hX : X = ⁅X,J⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer,hJmap]
    exact D.actor_eq_commutator_of_thompson_not_centralizes
      (source_module_nonsolvable_uniqueness D) hJ
  have hJY : J.map q ≤ Y := ChapterB.InternalThompsonAction.thompson_image_le S U
  calc
    X.map q = ⁅X.map q,J.map q⁆ := by rw [←map_commutator,←hX]
    _ ≤ ⁅X.map q,Y⁆ := commutator_mono le_rfl hJY
    _ ≤ Y := commutator_le_right _ _

/-- The complete B.5 two-factor theorem applies to the full module with
its literal M-centralizer quotient. No full/local equality is assumed. -/
theorem full_module_two_factor_case
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
      (ρ.comp (offenderSubgroup ρ).subtype)) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  have hU := source_full_module_reduced D
  let := hU.normal
  let := hU.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let σ := ρ.comp Y.subtype
  let X := (localOrbit T L).subgroupOf M
  have hXY : X.map q ≤ Y := full_orbit_image_le_offender D hJ
  have hsource := ChapterB.InternalThompsonAction.offender_hypothesis ρ q
    (QuotientGroup.mk'_surjective _)
    (D.simpleQTKE.twoLocal_sqtk (source_module_nonsolvable_uniqueness D).normalizer_maximal.1)
    (ChapterB.InternalThompsonAction.action_faithful U) hU.quotient_pCore_eq_bot
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let A := L.subgroupOf M
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let B := A.map (MulAut.conj tM).toMonoidHom
  obtain ⟨hAq,hBq,hne⟩ := full_action_component_pair D ht htn
  have hAX : A ≤ X := comap_mono (le_componentOrbit L T)
  have hBX : B ≤ X := by
    rintro b ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp tM.property a).mp (hAX ha)
  have hAY : A.map q ≤ Y := (map_mono hAX).trans hXY
  have hBY : B.map q ≤ Y := (map_mono hBX).trans hXY
  have hneY : (A.map q).subgroupOf Y ≠ (B.map q).subgroupOf Y := by
    intro he
    apply hne
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hBY] using hh
  have hclass := ChapterB.SourceInduction.adequateAlternative_knownSimple σ hsource
  rcases hclass.product_rows_of_two_components σ (hAq.subgroupOf hAY)
      (hBq.subgroupOf hBY) hneY with hp | hp
  · exact hp
  obtain ⟨hp⟩ := hp
  have hmU : ⁅U,X⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le
      (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer),
      map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer]
    exact (D.fullModule_eq_commutator (source_module_nonsolvable_uniqueness D)).symm
  have hmX : subspaceCommutator ρ ⊤ (X.map q) = ⊤ := by
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (X.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) X]
    ext w
    change (w.toMul : M) ∈ ⁅U,X⁆ ↔ True
    rw [hmU]
    exact iff_true_intro w.toMul.property
  have hmY : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator (ρ.comp Y.subtype) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map, ←MonoidHom.range_eq_map, range_subtype]
    apply top_unique
    calc
      ⊤ = subspaceCommutator ρ ⊤ (X.map q) := hmX.symm
      _ ≤ subspaceCommutator ρ ⊤ Y := Submodule.span_mono
        (by rintro _ ⟨g,hg,v,hv,rfl⟩; exact ⟨g,hXY hg,v,hv,rfl⟩)
  have hh := hp.hyperplane
  unfold ChapterB.QuasisimpleSource.moved at hh
  rw [hmY,top_sup_eq,Module.finrank_zero_of_subsingleton] at hh
  omega

/-- The full quotient component is isomorphic to the original intrinsic
L/O₂(L), through the original inclusion and centralizer quotient. -/
theorem full_action_original_component_equiv
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    Nonempty (((L.subgroupOf M).map q) ≃* (L ⧸ pCore 2 L)) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  let a : L ≃* A := (subgroupOfEquivOfLe hLM).symm
  let f := (q.subgroupMap A).comp a.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp a.surjective
  have hk : pCore 2 L ≤ f.ker := by
    intro l hl
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    exact Subtype.ext (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hl) v hv)
  let fbar := QuotientGroup.lift (pCore 2 L) f hk
  have hbar : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective _ _ hf hk
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hA := (full_action_component_pair D ht htn).1
  let : Nontrivial (A.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hA.isCComponent.ne_bot
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  have hi : Function.Injective fbar := by
    apply fbar.ker_eq_bot_iff.mp
    rcases fbar.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    exfalso
    obtain ⟨y,hy⟩ := exists_ne (1 : A.map q)
    obtain ⟨x,rfl⟩ := hbar y
    exact hy (show x ∈ fbar.ker from ht ▸ mem_top _)
  exact ⟨(MulEquiv.ofBijective fbar ⟨hi,hbar⟩).symm⟩

private theorem source_factor_eq_nonA5_component
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {F C : Subgroup Q} {U : Subrepresentation ρ}
    (hF : ChapterB.SourceInduction.SourceFactorCase ρ F U)
    (hC : IsComponent Q C) (hCF : C ≤ F)
    (hna : ¬ Nonempty (C ≃* alternatingGroup (Fin 5))) : C = F := by
  have hc := hC.subgroupOf hCF
  rcases hF.group_models with he | he | ⟨hs,_⟩
  · obtain ⟨e⟩ := he
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let := hc.2
    let : Nontrivial (C.subgroupOf F) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hc.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable (C.subgroupOf F) inferInstance).elim
  · obtain ⟨e⟩ := he
    let A := alternatingGroup (Fin 5)
    let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple A :=
      { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
        simple := ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hA : IsComponent (Equiv.Perm (Fin 5)) A :=
      ⟨(inferInstance : A.Normal).isSubnormal,inferInstance⟩
    have hec := hc.map_equiv e
    let := hec.2
    have heq : (C.subgroupOf F).map e.toMonoidHom = A := by
      apply hec.eq_of_le hA
      rw [←commutator_eq_self (H := (C.subgroupOf F).map e.toMonoidHom)]
      exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
    exact (hna ⟨(subgroupOfEquivOfLe hCF).symm.trans
      ((e.subgroupMap (C.subgroupOf F)).trans (MulEquiv.subgroupCongr heq))⟩).elim
  · let := hs
    have ht := hc.1.eq_bot_or_top_of_isSimpleGroup hs
    exact le_antisymm hCF (subgroupOf_eq_top.mp (ht.resolve_left hc.isCComponent.ne_bot))

/-- In the non-A₅ branch, the original components are the full B.5 factors,
not merely subgroups of them. The same specified quotient-image actions
therefore carry the original components. -/
theorem full_module_factor_alignment
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let Y := offenderSubgroup ρ
    let A := L.subgroupOf M
    let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
    let B := A.map (MulAut.conj tM).toMonoidHom
    ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype),
      ((A.map q).subgroupOf Y = d.first ∧ (B.map q).subgroupOf Y = d.second) ∨
      ((A.map q).subgroupOf Y = d.second ∧ (B.map q).subgroupOf Y = d.first) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let X := (localOrbit T L).subgroupOf M
  let A := L.subgroupOf M
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let B := A.map (MulAut.conj tM).toMonoidHom
  have hXY : X.map q ≤ Y := full_orbit_image_le_offender D hJ
  have hAX : A ≤ X := comap_mono (le_componentOrbit L T)
  have hBX : B ≤ X := by
    rintro b ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp tM.property a).mp (hAX ha)
  have hAY : A.map q ≤ Y := (map_mono hAX).trans hXY
  have hBY : B.map q ≤ Y := (map_mono hBX).trans hXY
  obtain ⟨hAq,hBq,hne⟩ := full_action_component_pair D ht htn
  have hneY : (A.map q).subgroupOf Y ≠ (B.map q).subgroupOf Y := by
    intro he
    apply hne
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hBY] using hh
  obtain ⟨a⟩ := full_action_original_component_equiv D (fun hn => htn (hn ht))
  have hBmap : B.map q = (A.map q).map (MulAut.conj (q tM)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  let b : (B.map q) ≃* (A.map q) := (MulEquiv.subgroupCongr hBmap).trans
    ((MulAut.conj (q tM)).subgroupMap (A.map q)).symm
  have hnaA : ¬ Nonempty (((A.map q).subgroupOf Y) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    exact hna ⟨a.symm.trans ((subgroupOfEquivOfLe hAY).symm.trans e)⟩
  have hnaB : ¬ Nonempty (((B.map q).subgroupOf Y) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    exact hna ⟨a.symm.trans (b.symm.trans ((subgroupOfEquivOfLe hBY).symm.trans e))⟩
  intro d
  rcases d.component_alignment (hAq.subgroupOf hAY) (hBq.subgroupOf hBY) hneY with
    ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨source_factor_eq_nonA5_component d.firstCase (hAq.subgroupOf hAY) ha hnaA,
      source_factor_eq_nonA5_component d.secondCase (hBq.subgroupOf hBY) hb hnaB⟩
  · exact Or.inr ⟨source_factor_eq_nonA5_component d.secondCase (hAq.subgroupOf hAY) ha hnaA,
      source_factor_eq_nonA5_component d.firstCase (hBq.subgroupOf hBY) hb hnaB⟩

/-- For the non-A₅ moving row, the full offender subgroup is exactly the
image of the original component orbit in M/C_M(V). -/
theorem full_offender_eq_orbit_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    offenderSubgroup ρ = ((localOrbit T L).subgroupOf M).map q := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let X := (localOrbit T L).subgroupOf M
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let A := L.subgroupOf M
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let B := A.map (MulAut.conj tM).toMonoidHom
  have hAX : A ≤ X := comap_mono (le_componentOrbit L T)
  have hBX : B ≤ X := by
    rintro b ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp tM.property a).mp (hAX ha)
  obtain ⟨d⟩ := full_module_two_factor_case D hn hJ
  have htop : (⊤ : Subgroup Y) ≤ (X.map q).subgroupOf Y := by
    rw [←d.product.sup_eq_top]
    rcases full_module_factor_alignment D hna hJ ht htn d with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [←ha,←hb]
      exact sup_le (comap_mono (map_mono hAX)) (comap_mono (map_mono hBX))
    · rw [←ha,←hb]
      exact sup_le (comap_mono (map_mono hBX)) (comap_mono (map_mono hAX))
  exact le_antisymm (fun y hy => htop (show (⟨y,hy⟩ : Y) ∈ ⊤ from mem_top _))
    (full_orbit_image_le_offender D hJ)

/-- The full two-factor classification is on the literal image of L₀ in
M/C_M(V), so its invariant quotient uses the original L₀-fixed layer. -/
theorem full_module_two_factor_case_on_orbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
      (ρ.comp (((localOrbit T L).subgroupOf M).map q).subtype)) := by
  have hd := full_module_two_factor_case D hn hJ
  dsimp only at hd ⊢
  rwa [full_offender_eq_orbit_image D hn hna hJ] at hd

private theorem full_source_first_fixed {Q V : Type*} [Group Q] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
    (d : ChapterB.SourceInduction.SourceTwoFactorCase ρ)
    (B : Subgroup Q) [Group.IsPerfect B] (hB : B ≤ d.second) :
    d.firstSpace.toSubmodule ≤ fixedSpace ρ B := by
  apply le_fixedSpace_of_commutator_le_fixedSpace ρ B d.firstSpace.toSubmodule
    (le_subspaceStabilizer _ _ (fun b _ v hv => d.firstSpace.apply_mem_toSubmodule b hv))
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,hv,rfl⟩
  have hh := congrArg Subtype.val (d.second_fixes_first ⟨b,hB hb⟩
    ⟨ρ.invariants.mkQ v, ⟨v,hv,rfl⟩⟩)
  have hz : ρ.invariants.mkQ (ρ b v - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hh
  exact fun b' => (Submodule.Quotient.mk_eq_zero _).mp hz b'

private theorem full_source_two_factor_crossed {Q V : Type*} [Group Q] [Finite Q]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
    (d : ChapterB.SourceInduction.SourceTwoFactorCase ρ)
    {A B : Subgroup Q} (hA : IsComponent Q A) (hB : IsComponent Q B) (hne : A ≠ B) :
    subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  let := hB.2
  rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact (Submodule.span_mono (by
      rintro _ ⟨a,ha',v,hv,rfl⟩
      exact ⟨a,ha ha',v,hv,rfl⟩)).trans
      (d.firstCase.moved_le_space.trans (full_source_first_fixed d B hb))
  · let d' : ChapterB.SourceInduction.SourceTwoFactorCase ρ := {
      first := d.second
      second := d.first
      product := d.product.swap
      firstSpace := d.secondSpace
      secondSpace := d.firstSpace
      decomposition := d.decomposition.symm
      firstCase := d.secondCase
      secondCase := d.firstCase }
    exact (Submodule.span_mono (by
      rintro _ ⟨a,ha',v,hv,rfl⟩
      exact ⟨a,ha ha',v,hv,rfl⟩)).trans
      (d.secondCase.moved_le_space.trans (full_source_first_fixed d' B hb))

/-- Local Thompson movement separates the entire full module on the original pair. -/
theorem full_moved_centralizes_partner
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let H := D.maximalLocal
  let U := D.fullModule.subgroupOf H
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let σ := ρ.comp Y.subtype
  let X := (localOrbit T L).subgroupOf H
  let A := L.subgroupOf H
  let tH : H := ⟨t,(le_normalizer_componentOrbit L T) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hLH : L ≤ H := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hUH : D.fullModule ≤ H :=
    D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have hXY : X.map q ≤ Y := full_orbit_image_le_offender D hJ
  have hAX : A ≤ X := comap_mono (le_componentOrbit L T)
  have hBX : B ≤ X := by
    rintro b ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp tH.property a).mp (hAX ha)
  have hAY : A.map q ≤ Y := (map_mono hAX).trans hXY
  have hBY : B.map q ≤ Y := (map_mono hBX).trans hXY
  obtain ⟨hAq,hBq,hne⟩ := full_action_component_pair D ht htn
  have hneY : (A.map q).subgroupOf Y ≠ (B.map q).subgroupOf Y := by
    intro he
    apply hne
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hBY] using hh
  obtain ⟨d⟩ := full_module_two_factor_case D (fun hn => htn (hn ht)) hJ
  have hc := full_source_two_factor_crossed d (hAq.subgroupOf hAY) (hBq.subgroupOf hBY) hneY
  have hcross : ⁅U,A⁆ ≤ centralizer (B : Set H) := by
    intro v hv b hb
    let w : Additive U := Additive.ofMul ⟨v,(commutator_le_left U A) hv⟩
    have hw : w ∈ subspaceCommutator ρ ⊤ (A.map q) := by
      change w ∈ subspaceCommutator
        (NormalElementaryQuotient.representation U q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (A.map q)
      rw [← NormalElementaryQuotient.commutatorSpace_eq U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)]
      exact hv
    have hw' : w ∈ subspaceCommutator σ ⊤ ((A.map q).subgroupOf Y) := by
      rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAY]
      exact hw
    have hbq : q b ∈ B.map q := mem_map_of_mem q hb
    have he := hc hw' (⟨⟨q b,hBY hbq⟩,hbq⟩ : (B.map q).subgroupOf Y)
    have he' := congrArg (fun z : Additive U => (z.toMul : H)) he
    change ((ρ (q b) w).toMul : H) = v at he'
    rw [ChapterB.InternalThompsonAction.action_apply] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hmapU : U.map H.subtype = D.fullModule := map_subgroupOf_eq_of_le hUH
  intro v hv b hb
  rw [←hmapU,←hmapA,←map_commutator] at hv
  rw [←hmapB] at hb
  obtain ⟨v,hv,rfl⟩ := hv
  obtain ⟨b,hb,rfl⟩ := hb
  exact congrArg H.subtype (hcross hv b hb)

/-- Crossed centralization follows directly on the full module, without
using reselection minimality or a full/local identification. -/
theorem crossed_of_local_thompson
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_opposite_centralization D ht htn
    (full_moved_centralizes_partner D hJ ht htn)

/-- The positive full-fixed-layer source branch also needs no minimality
assumption to separate the two full moved factors. -/
theorem crossed_of_full_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_local_thompson D
    (local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed) ht htn

/-- The full B.5 classification in the positive fixed-layer branch uses only
the original source assumptions and the actual full action. -/
theorem full_module_two_factor_case_of_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
      (ρ.comp (offenderSubgroup ρ).subtype)) :=
  full_module_two_factor_case D hn
    (local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed)


end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
