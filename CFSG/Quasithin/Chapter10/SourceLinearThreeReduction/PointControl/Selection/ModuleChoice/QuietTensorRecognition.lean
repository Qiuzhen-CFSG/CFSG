module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCoordinates
public import Theory.Representation.BinaryTensorThree.SwappedRecognition
public import Theory.Representation.PSL3Two.SteinbergSquare
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# Recognizing the original quiet binary-three tensor action

When the original homogeneous seed is the full module, its restriction to the
original component square is irreducible. Conjugation by the specified element
of T exchanges the two quotient factors. The binary SL₃ catalogue reconstructs
the natural tensor with its literal orbit action image. The other catalogue
alternative, the Steinberg square, contradicts the original full action cubic
bound. The full action kernel, both quotient maps and the original conjugator
are retained; dimension is not used as recognition.

Source: Aschbacher--Smith original 3.2.6(2), printed p.581, and the quiet
case of 10.1.1--3, printed pp.741--742 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.QuadraticFourGroup.TensorClassification
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- When the source seed is the full module, the actual binary-three square
has natural tensor coordinates. Its action image is exactly the tensor base,
and the original full action cubic bound excludes the Steinberg alternative. -/
theorem quiet_binaryThree_seed_eq_full_tensor_coordinates
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hseed : D.seed = D.fullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space,
      ((localOrbit T L).subgroupOf (localJoin T L)).map
        (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range := by
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let qM := ChapterB.InternalThompsonAction.actionMk U
  let ρ₀ := ChapterB.InternalThompsonAction.action U
  have hVM : D.fullModule ≤ D.maximalLocal :=
    D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let aV : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    a.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul a.toAdditive.toAddMonoidHom c v)
  let ρ : Representation (ZMod 2) _ (Additive D.fullModule) :=
    (aV.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ₀
  have hρ : Function.Injective ρ := (aV.conjAlgEquiv (ZMod 2)).injective.comp
    (ChapterB.InternalThompsonAction.action_faithful U)
  have hρact (m : D.maximalLocal) (v : D.fullModule) :
      ((ρ (qM m) (Additive.ofMul v)).toMul : G) = (m:G)*(v:G)*(m:G)⁻¹ := by
    change (((ρ₀ (qM m) (aV.symm (Additive.ofMul v))).toMul : D.maximalLocal) : G) = _
    exact congrArg (fun x : D.maximalLocal => (x : G))
      (ChapterB.InternalThompsonAction.action_apply U m (aV.symm (Additive.ofMul v)))
  obtain ⟨p,hp,hpk,hl,hr⟩ := original_component_product_quotient D hn ht htn
  obtain ⟨i,hi,hin,hcompat⟩ := original_component_product_embedding D hn p hp hpk
  obtain ⟨α,hα⟩ := original_component_product_exchange D hn ht htn p hl hr
  let c := cL.prodCongr cL
  let q := c.toMonoidHom.comp p
  have hq : Function.Surjective q := c.surjective.comp hp
  let j := i.comp c.symm.toMonoidHom
  let σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
      (Additive D.fullModule) := ρ.comp j
  have hσ : Function.Injective σ := hρ.comp (hi.comp c.symm.injective)
  have hact (g : localOrbit T L) (v : D.fullModule) :
      ((σ (q g) (Additive.ofMul v)).toMul : G) = (g:G)*(v:G)*(g:G)⁻¹ := by
    change ((ρ (i (c.symm (c (p g)))) (Additive.ofMul v)).toMul : G) = _
    rw [c.symm_apply_apply,hcompat]
    exact hρact _ v
  let s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥ (σ.comp q) := {
    section_le := D.fullModule_le_orbit
    kernel_le := bot_le
    normalized := (localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule
    coordinates := { toFun v := Multiplicative.ofAdd (Additive.ofMul v)
                     map_one' := rfl
                     map_mul' _ _ := rfl }
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext v
      change v = 1 ↔ (v : G) = 1
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    equivariant := by
      intro g v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (hact g v).symm }
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  let : ρ₀.IsIrreducible := quiet_full_action_irreducible D hmany hmin hJ
  let : Nontrivial (Additive U) := Subrepresentation.irreducible_module_nontrivial ρ₀
  let : Nontrivial (Additive D.fullModule) := aV.symm.toEquiv.nontrivial
  have hσirr : σ.IsIrreducible := by
    apply (irreducible_comp_surjective_iff q hq σ).mp
    apply s.irreducible_of_subgroup_minimal
    intro A hAV hAN
    rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus A
      (by change A ≤ D.seed; rw [hseed]; exact hAV) hAN with he | hc
    · exact Or.inl (he.trans hseed)
    · exact Or.inr ((le_inf hAV hc).trans_eq
        (source_fullModule_fixed_eq_bot_of_many D hmany hJ))
  let := hσirr
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv
    (ρ.asGroupHom (qM ⟨t,le_normalizer_componentOrbit L T ht⟩))
  have hex (g : BinaryLinearThree.Group) (v : Additive D.fullModule) :
      E (σ (g,1) v) = σ (1,g) (E v) := by
    have he : i (1,cL.symm g) =
        qM ⟨t,le_normalizer_componentOrbit L T ht⟩ * i (cL.symm g,1) *
          (qM ⟨t,le_normalizer_componentOrbit L T ht⟩)⁻¹ := by
      obtain ⟨x,hx⟩ := hp (cL.symm g,1)
      have hh := hα x
      rw [hx,map_one] at hh
      rw [←hh,←hx,hcompat,hcompat]
      change qM ⟨t*(x:G)*t⁻¹,_⟩ = _
      simp only [←map_inv]
      rfl
    change ρ (qM ⟨t,_⟩) (ρ (i (cL.symm g,cL.symm 1)) v) =
      ρ (i (cL.symm 1,cL.symm g)) (ρ (qM ⟨t,_⟩) v)
    simp only [map_one,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v) (mul_inv_eq_iff_eq_mul.mp he.symm)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  let : Nontrivial BinaryLinearThree.Group := cL.symm.toEquiv.nontrivial
  have hleft : ∃ g, σ (g,1) ≠ 1 := by
    obtain ⟨g,hg⟩ := exists_ne (1 : BinaryLinearThree.Group)
    exact ⟨g,fun hh => hg (congrArg Prod.fst (hσ (hh.trans σ.map_one.symm)))⟩
  rcases BinaryTensorThree.exchanged_irreducible_alternatives σ hleft E hex with hn | hs
  · obtain ⟨b,⟨e⟩⟩ := hn
    refine ⟨e.toLinearEquiv,?_⟩
    have he (g : localOrbit T L) :
        quietTensorLinearAction D e.toLinearEquiv
          ⟨g,(show localOrbit T L ≤ localJoin T L from le_sup_left) g.property⟩ =
          BinaryTensorThree.baseAction (b (q g)) := by
      apply LinearEquiv.ext
      intro w
      obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
      rw [quietTensorLinearAction_apply]
      have ha : Additive.ofMul (D.fullModule.normalizerMonoidHom
          ⟨g,D.maximalLocal_normalizes_fullModule ((localOrbit T L).le_normalizer g.property)⟩ v.toMul) = σ (q g) v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hact g v.toMul).symm
      rw [ha]
      exact LinearMap.congr_fun (e.isIntertwining' (q g)) v
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact ⟨b (q ⟨g,hg⟩),(he ⟨g,hg⟩).symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨x,hx⟩ := (b.surjective.comp hq) g
      refine ⟨⟨x,(show localOrbit T L ≤ localJoin T L from le_sup_left) x.property⟩,x.property,?_⟩
      rw [he]
      exact congrArg BinaryTensorThree.baseAction hx
  · obtain ⟨e⟩ := hs
    have hjrange : j.range = i.range := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨c.symm x,rfl⟩
      · rintro ⟨x,rfl⟩
        refine ⟨c x,?_⟩
        change i (c.symm (c x)) = i x
        rw [c.symm_apply_apply]
    let : j.range.Normal := by rw [hjrange]; exact hin
    have hρc : Representation.BinaryOffender.cubicRatio ρ ≤ 2 :=
      Representation.BinaryOffender.cubicRatio_le_nat_of_equivariant ρ₀ ρ
        (MonoidHom.id _) Function.injective_id aV (by
          intro g v
          change aV (ρ₀ g v) = aV (ρ₀ g (aV.symm (aV v)))
          rw [aV.symm_apply_apply]) 2
        (source_full_module_cubic_bound_of_many D hmany)
    exact False.elim (BinaryLinearThree.SteinbergSquare.not_cubic_normal_extension
      ρ hρ j (hi.comp c.symm.injective) hσirr e hρc)
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
