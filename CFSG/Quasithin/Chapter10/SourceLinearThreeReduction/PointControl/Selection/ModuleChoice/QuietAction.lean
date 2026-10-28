module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.FullRows
public import CFSG.Quasithin.Chapter10.SourceA5NumericalSelection
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductExchange
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Thompson

/-!
# Literal actions and fixed support in the centralizing local Thompson branch

When J(T) centralizes the local module, the ambient multiple-overgroup
hypothesis kills the full L₀-fixed layer. Minimality then makes the faithful
full M-action irreducible. The original pair gives a normally embedded product
of the actual simple component quotients, with both factor inclusions and
the exchanger retained.

A nonzero component-fixed vector yields nonzero opposite fixed support;
minimality gives crossed centralization. If J(T) also centralizes the full
module, the original Thompson consumer supplies every point-Sylow conclusion.
Existence of component-fixed vectors, and the case of local centralization
with full movement, remain to be proved by the source assembly.

Source: Aschbacher--Smith, 3.2.6, 3.2.10(8--9), 10.1.1--2 and 10.2.9,
printed pp.581,583--584,741--742,750.
-/

public noncomputable section
open scoped IsMulCommutative

open Subgroup Theory.GroupTheory Representation Stellmacher
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The actual component pair has its intrinsic two-core product quotient. -/
theorem original_component_product_quotient
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
        (QuotientGroup.mk' _ l,1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) =
        (1,QuotientGroup.mk' _ l)) := by
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut R := ((MulAut.conj t).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  obtain ⟨q,hq,hk,hfirst,hsecond⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  refine ⟨q,hq,hk,?_,?_⟩
  · intro l
    exact hfirst (a.symm l)
  · intro l
    have hh := hsecond (b (a.symm l))
    change q (originalConjugateOrbitInclusion ht l) =
      (1,eA (QuotientGroup.mk' _ (b.symm (b (a.symm l))))) at hh
    rw [b.symm_apply_apply] at hh
    exact hh

/-- The literal product embeds normally in the faithful full-module actor. -/
theorem original_component_product_embedding
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (q : localOrbit T L →* (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L))
    (hq : Function.Surjective q) (hqk : q.ker = pCore 2 (localOrbit T L)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    ∃ i : (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L) →*
        (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)),
      Function.Injective i ∧ i.range.Normal ∧
      ∀ x : localOrbit T L,
        i (q x) = QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
          (inclusion (localOrbit T L).le_normalizer x) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set M))
  let f := qM.comp (inclusion R.le_normalizer)
  have hk : q.ker = f.ker := hqk.trans (full_actor_restriction_kernel D hn).symm
  let i := q.liftOfSurjective hq ⟨f,hk.le⟩
  have hi (x : R) : i (q x) = f x := q.liftOfRightInverse_comp_apply _ _ _ x
  refine ⟨i,?_,?_,hi⟩
  · apply (MonoidHom.ker_eq_bot_iff i).mp
    apply le_bot_iff.mp
    intro a ha
    obtain ⟨x,rfl⟩ := hq a
    have hx : x ∈ f.ker := (hi x).symm.trans ha
    exact (show x ∈ q.ker from hk.symm ▸ hx)
  · have hf : f.range = (R.subgroupOf M).map qM := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    have hir : i.range = f.range := by
      ext y
      constructor
      · rintro ⟨a,rfl⟩
        obtain ⟨x,rfl⟩ := hq a
        exact ⟨x,(hi x).symm⟩
      · rintro ⟨x,rfl⟩
        exact ⟨q x,hi x⟩
    rw [hir,hf]
    exact (normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (R : Set G)
      from le_rfl)).map qM (QuotientGroup.mk'_surjective _)

include D in
/-- The specified Sylow exchanger swaps the marked factors, with its actual square twist. -/
theorem original_component_product_exchange
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (q : localOrbit T L →* (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
      (QuotientGroup.mk' _ l,1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) =
      (1,QuotientGroup.mk' _ l)) :
    ∃ α : MulAut (L ⧸ pCore 2 L), ∀ x : localOrbit T L,
      q (originalOrbitConjugation ht x) = (α (q x).2,(q x).1) := by
  let R := localOrbit T L
  let A := L.subgroupOf R
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf R
  let τ := originalOrbitConjugation (L := L) ht
  let β := QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
    (pCore_map_iso 2 (originalSquareConjugation D hn ht))
  let f := q.comp τ.toMonoidHom
  let g := ((β.toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)).comp q
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup (le_componentOrbit L T) (le_sup_right.trans hp.le),hp,subgroupOf_self]
  have hA : A ≤ f.eqLocus g := by
    intro a ha
    let l : L := ⟨a,ha⟩
    change q (τ a) = (β (q a).2,(q a).1)
    have hl : q a = (QuotientGroup.mk' _ l,1) := hfirst l
    have hr : q (τ a) = (1,QuotientGroup.mk' _ l) := hsecond l
    rw [hl,hr]
    exact Prod.ext β.map_one.symm rfl
  have hB : B ≤ f.eqLocus g := by
    intro b hb
    obtain ⟨l,hl,he⟩ := mem_map.mp hb
    let l' : L := ⟨l,hl⟩
    have hb' : b = originalConjugateOrbitInclusion ht l' := Subtype.ext he.symm
    subst b
    change q (τ (originalConjugateOrbitInclusion ht l')) =
      (β (q (originalConjugateOrbitInclusion ht l')).2,
        (q (originalConjugateOrbitInclusion ht l')).1)
    rw [hsecond l']
    let l₂ := originalSquareConjugation D hn ht l'
    have he₂ : τ (originalConjugateOrbitInclusion ht l') =
        (⟨l₂,le_componentOrbit L T l₂.property⟩ : R) := by
      apply Subtype.ext
      change t * (t * l * t⁻¹) * t⁻¹ = (t*t) * l * (t*t)⁻¹
      simp only [mul_inv_rev,mul_assoc]
    rw [he₂,hfirst l₂]
    rfl
  exact ⟨β,fun x => (sup_le hA hB) (hgen.symm ▸ mem_top x)⟩


/-- Vanishing of the original orbit-fixed layer promotes minimality to irreducibility. -/
theorem quiet_full_action_irreducible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    (ChapterB.InternalThompsonAction.action U).IsIrreducible := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let e : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  have hU : U ≠ ⊥ := by
    intro hz
    have hh := congrArg (map M.subtype) hz
    rw [map_subgroupOf_eq_of_le hVM, Subgroup.map_bot] at hh
    exact D.module_ne_bot (bot_unique ((le_componentOrbit _ _).trans_eq hh))
  let : Nontrivial U := (nontrivial_iff_ne_bot _).mpr hU
  let c : BinaryConjugationSection M D.fullModule ⊥ (ρ.comp q) := {
    section_le := hVM
    kernel_le := bot_le
    normalized := D.maximalLocal_normalizes_fullModule
    coordinates := {
      toFun v := Multiplicative.ofAdd (Additive.ofMul (e.symm v))
      map_one' := e.symm.map_one
      map_mul' := e.symm.map_mul }
    onto := fun w => ⟨e w.toAdd.toMul, e.symm_apply_apply _⟩
    kernel_eq := by
      ext v
      change e.symm v = 1 ↔ (v : G) = 1
      rw [map_eq_one_iff e.symm e.symm.injective]
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    equivariant := by
      intro m v
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg M.subtype (ChapterB.InternalThompsonAction.action_apply U m
        (Additive.ofMul (e.symm v)))).symm }
  apply (irreducible_comp_surjective_iff q (QuotientGroup.mk'_surjective _) ρ).mp
  apply c.irreducible_of_subgroup_minimal
  intro A hAV hAN
  rcases source_minimal_fullModule_eq_or_le_centralizer D hmin A hAN hAV with he | hc
  · exact Or.inl he
  · exact Or.inr ((le_inf hAV hc).trans_eq (source_fullModule_fixed_eq_bot_of_many D hmany hJ))

/-- Conjugation transports the whole original component-fixed subgroup. -/
theorem quiet_component_fixed_conjugate
    {t : G} (ht : t ∈ (T : Subgroup G)) :
    (D.fullModule ⊓ centralizer (L : Set G)).map (MulAut.conj t).toMonoidHom =
      D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  have he : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
  rw [map_inf _ _ _ (MulAut.conj t).injective,Theory.GroupTheory.map_centralizer_equiv,he]
  rfl

/-- A nonzero component-fixed subgroup is moved by the opposite component. -/
theorem quiet_fixed_support_of_component_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hfix : D.fullModule ⊓ centralizer (L : Set G) ≠ ⊥) :
    ⁅D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G),L⁆ ≠ ⊥ := by
  let B := L.map (MulAut.conj t).toMonoidHom
  have hpair : localOrbit T L = L ⊔ B := componentOrbit_eq_sup_of_index_two L T
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
      (fun hn => htn (hn ht))) inf_le_right ht htn
  have hzero := source_fullModule_fixed_eq_bot_of_many D hmany hJ
  intro hm
  have hc := commutator_eq_bot_iff_le_centralizer.mp hm
  have hb : D.fullModule ⊓ centralizer (B : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    apply hzero.le
    refine ⟨hv.1,?_⟩
    have hh : localOrbit T L ≤ centralizer ({v} : Set G) := by
      rw [hpair]
      exact sup_le (fun l hl => mem_centralizer_singleton_iff.mpr (hc hv l hl))
        (fun b hb => mem_centralizer_singleton_iff.mpr (hv.2 b hb))
    exact fun x hx => mem_centralizer_singleton_iff.mp (hh hx)
  apply hfix
  apply (map_eq_bot_iff_of_injective (f := (MulAut.conj t).toMonoidHom) _ (MulAut.conj t).injective).mp
  exact (quiet_component_fixed_conjugate D ht).trans hb

/-- Minimality promotes the nonzero fixed support to crossed centralization. -/
theorem quiet_crossed_of_component_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hfix : D.fullModule ⊓ centralizer (L : Set G) ≠ ⊥) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_minimal_fixed_support D hmin ht htn
    (quiet_fixed_support_of_component_fixed_ne_bot D hmany hJ ht htn hfix)

/-- The quiet source branch has a faithful irreducible full action with the
original cubic bound and a normally embedded product of the original simple
quotients. Both factor formulas use the original inclusion and exchanger. -/
theorem quiet_original_product_action
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let qM := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Representation.BinaryOffender.cubicRatio ρ ≤ 2 ∧
      ∃ q : localOrbit T L →* (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L),
        Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
        (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
          (QuotientGroup.mk' _ l,1)) ∧
        (∀ l : L, q (originalConjugateOrbitInclusion ht l) =
          (1,QuotientGroup.mk' _ l)) ∧
        ∃ i : (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L) →*
            (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)),
          Function.Injective i ∧ i.range.Normal ∧
          (∀ x : localOrbit T L, i (q x) = qM (inclusion (localOrbit T L).le_normalizer x)) ∧
          ∃ α : MulAut (L ⧸ pCore 2 L), ∀ g,
            i (α g.2,g.1) =
              qM ⟨t,le_normalizer_componentOrbit L T ht⟩ * i g *
                (qM ⟨t,le_normalizer_componentOrbit L T ht⟩)⁻¹ := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  refine ⟨ChapterB.InternalThompsonAction.action_faithful U,
    quiet_full_action_irreducible D hmany hmin hJ,
    source_full_module_cubic_bound_of_many D hmany,?_⟩
  obtain ⟨q,hq,hk,hl,hr⟩ := original_component_product_quotient D hn ht htn
  obtain ⟨i,hi,hin,hcompat⟩ := original_component_product_embedding D hn q hq hk
  obtain ⟨α,hα⟩ := original_component_product_exchange D hn ht htn q hl hr
  refine ⟨q,hq,hk,hl,hr,i,hi,hin,hcompat,α,?_⟩
  intro g
  obtain ⟨x,rfl⟩ := hq g
  rw [←hα,hcompat,hcompat]
  change _ = (QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))) ⟨t,_⟩ *
    (QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))) ⟨x,_⟩ *
    ((QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))) ⟨t,_⟩)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  rfl

/-- In the quiet branch, a nonzero component-fixed subgroup supplies the
original support row and every point-Sylow conclusion. There is no natural
model, fixed-kernel, half-Sylow or stabilizer-normalizer premise in this branch. -/
theorem exists_point_selection_of_quiet_component_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (hfix : D.fullModule ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      ⁅D.fullModule ⊓ centralizer
        (L.map (MulAut.conj t).toMonoidHom : Set G),L⁆ ≠ ⊥ ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
      PointSylowControl D t := by
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hlocal := hJ.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal))
  have hs := quiet_fixed_support_of_component_fixed_ne_bot D hmany hlocal ht htn hfix
  have hc := crossed_of_minimal_fixed_support D hmin ht htn hs
  exact ⟨t,ht,htn,hs,hc,pointSylowControl_of_thompson_centralizes D hmany ht htn hc hJ⟩

/-- The unresolved quiet-support case has no nonidentity vector fixed by
either original component. The other branch already supplies the literal
support and point-control conclusions. Excluding the fixed-free branch is
still required for FixedSupportRowsAt. -/
theorem quiet_support_or_component_fixed_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    (∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      ⁅D.fullModule ⊓ centralizer
        (L.map (MulAut.conj t).toMonoidHom : Set G),L⁆ ≠ ⊥ ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
      PointSylowControl D t) ∨
    (D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
      ∀ t ∈ (T : Subgroup G),
        D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) = ⊥) := by
  by_cases hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥
  · refine Or.inr ⟨hfix,fun t ht => ?_⟩
    rw [←quiet_component_fixed_conjugate D ht,hfix,Subgroup.map_bot]
  · exact Or.inl (exists_point_selection_of_quiet_component_fixed_ne_bot D hmany hmin hn hJ hfix)


end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
