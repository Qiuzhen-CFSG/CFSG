module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPlaneFixed
public import Theory.Representation.BinaryTensorThree.PlaneFixedAction
public import CFSG.Quasithin.ChapterE.Section04.Solvable
public import CFSG.Quasithin.ChapterE.Section03.OddCore

/-!
# The original tensor fixed four-space inside C₁(T,V)

For each corank-one subgroup A of a conjugate of V in T, source E.3.7
makes every index-at-most-two subgroup of A have the same fixed space in V.
These equalities restrict to the constructed plane-radical fixed four-space.
Its faithful plane-parabolic action image is solvable with trivial two-core,
so E.3.40 and solvable Fitting theory force the A-image to be trivial.
Thus the literal U=C_V(R) lies in C₁(T,V), without requiring W₁(T,V) to
centralize all of V. The Source application combines this with the proved
Held bound C_G(U)≤M to obtain C_G(C₁(T,V))≤M.

The generation step of 8.3.9, final Held exclusion, tensor recognition and
both quiet exclusions remain source obligations. All original action
kernels, Sylow subgroups and tensor markings are retained.
Source: Aschbacher--Smith E.3.7, E.3.40, E.4.1 and 8.3.3,8.3.9,
printed pp.231,240--241,723,725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Representation.BinaryOffender
open BinaryTensorThree.PlaneFixed

/-- Fixed-space rigidity at index at most two annihilates the solvable
plane-parabolic image on its radical fixed space. -/
theorem line_action_trivial_of_rigidity
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (f : A →* Line)
    (hfix : ∀ B : Subgroup A, Nat.log 2 B.index < 2 →
      ∀ X : square, (∀ b : B, lineAction (f b.val) X = X) →
        ∀ a : A, lineAction (f a) X = X) :
    ∀ a : A, lineAction (f a) = 1 := by
  let I := lineAction.asGroupHom.range
  let : Finite I := Finite.of_surjective _ lineAction.asGroupHom.rangeRestrict_surjective
  let σ : Representation (ZMod 2) I square :=
    (Units.coeHom (Module.End (ZMod 2) square)).comp I.subtype
  have hσ : Function.Injective σ := by
    intro x y he
    exact Subtype.ext (Units.ext he)
  have hbound : moduleA σ ≤ 1 :=
    moduleA_le_one_of_oddCore_centralization σ lineAction_image_solvable
      lineAction_image_twoCore (fun _ ha => lemma_E_3_40 σ hσ ha)
  let t : A →* I := lineAction.asGroupHom.rangeRestrict.comp f
  have ht : t.range = ⊥ := by
    by_contra hne
    have hfam : t.range ∈ fixedSpaceFamily σ 2 := by
      refine ⟨by decide,⟨hne,IsElementaryAbelian.of_surjective _ t.rangeRestrict_surjective⟩,?_⟩
      intro B hB hb
      apply le_antisymm (Representation.BinaryOffender.fixedSpace_antitone σ hB)
      intro X hX a
      obtain ⟨a,ha⟩ := a.property
      have h := hfix (B.comap t) (by rwa [index_comap]) X (fun b =>
        hX ⟨t b.val,b.property⟩) a
      change σ (t a) X = X at h
      rwa [ha] at h
    have hh := (le_moduleA_of_mem σ hfam).trans hbound
    norm_num at hh
  intro a
  have he : t a = 1 := mem_bot.mp (ht ▸ (show t a ∈ t.range from ⟨a,rfl⟩))
  exact congrArg (fun x : I => x.val.val) he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The literal fixed four-space lies in C₁(T,V). Each corank-one
conjugate subgroup acts trivially on it by E.3.7 and the solvable action
image, retaining the original full module, Sylow and tensor marking. -/
theorem quiet_tensor_plane_fixed_le_weakCentralizer
    (hs : globalS D.fullModule = 3)
    (q : localJoin T L →* Actor) (hq : Function.Surjective q)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hT : ((T : Subgroup G).subgroupOf (localJoin T L)).map q = Matrix.PSL3Two.WreathPair.borel)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v)) :
    originalFixed D.fullModule (localJoin T L) q ≤
      weakCentralizer D.fullModule (T : Subgroup G) 1 := by
  let V := D.fullModule
  let H := localJoin T L
  have hVN : H ≤ normalizer (V : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  have he (a : H) (v : Additive V) :
      b (Additive.ofMul (V.normalizerMonoidHom ⟨a,hVN a.property⟩ v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v) := by
    rw [←quietTensorLinearAction_apply D b]
    exact hb a v
  have hU : originalFixed V H q ≤ centralizer (indexedWeakClosure V (T : Subgroup G) 1 : Set G) := by
    apply le_centralizer_iff.mp
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    rintro A ⟨⟨g,hAg,hi⟩,hAT⟩
    let W := V.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 A :=
      IsElementaryAbelian.of_injective (inclusion hAg) (inclusion_injective hAg)
    have hAH : A ≤ H := hAT.trans le_sup_right
    let f : A →* Line :=
      (q.comp (inclusion hAH)).codRestrict Line (fun a =>
        Matrix.PSL3Two.WreathPair.borel_le_line
          (hT ▸ mem_map_of_mem q (hAT a.property)))
    have hf := line_action_trivial_of_rigidity f (by
      intro B hB X hX a
      let B' := B.map A.subtype
      have hBA : B' ≤ A := map_subtype_le B
      have hidx : B'.relIndex A = B.index := by
        change (B.map A.subtype).relIndex A = B.index
        rw [relIndex,subgroupOf,comap_map_eq_self_of_injective A.subtype_injective]
      have hcor : (subgroupCorank W B' : ℕ∞) < globalS V := by
        rw [hs]
        apply ENat.natCast_lt_natCast.mpr
        unfold subgroupCorank
        apply Nat.log_lt_of_lt_pow' (by decide)
        rw [←relIndex_mul_relIndex B' A W hBA hAg,hidx,hi]
        have hh := Nat.lt_pow_of_log_lt (by decide : 1 < 2) hB
        norm_num at hh ⊢
        omega
      let v := b.symm X.val
      have hvB : (v.toMul : G) ∈ V ⊓ centralizer (B' : Set G) := by
        refine ⟨v.toMul.property,?_⟩
        rintro x ⟨x,hx,rfl⟩
        have hh := congrArg Subtype.val (hX ⟨x,hx⟩)
        change BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q (inclusion hAH x))) X.val = X.val at hh
        have hbv : b v = X.val := b.apply_symm_apply X.val
        rw [←hbv,←he] at hh
        have hv := congrArg (fun w : Additive V => (w.toMul : G)) (b.injective hh)
        exact mul_inv_eq_iff_eq_mul.mp hv
      have hc := lemma_E_3_7 g (le_inf (hBA.trans hAg) ((hBA.trans hAH).trans hVN)) hcor
      have hvW : (v.toMul : G) ∈ V ⊓ centralizer (W : Set G) := hc ▸ hvB
      have hcomm := hvW.2 a.val (hAg a.property)
      have hv : V.normalizerMonoidHom ⟨inclusion hAH a,hVN (hAH a.property)⟩ v.toMul = v.toMul := by
        apply Subtype.ext
        change a.val*(v.toMul : G)*a.val⁻¹ = v.toMul
        rw [hcomm,mul_inv_cancel_right]
      apply Subtype.ext
      change BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q (inclusion hAH a))) X.val = X.val
      rw [←b.apply_symm_apply X.val,←he,hv]
      rfl
    )
    intro a ha u hu
    let v : V := ⟨u,hu.1⟩
    have hx := (mem_originalFixed V H hVN q hq b he v).mp hu
    have hh := congrArg (fun f : Module.End (ZMod 2) square => (f ⟨b (Additive.ofMul v),hx⟩).val) (hf ⟨a,ha⟩)
    change BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q ⟨a,hAH ha⟩)) (b (Additive.ofMul v)) = b (Additive.ofMul v) at hh
    rw [←he] at hh
    have hv := congrArg (fun w : Additive V => (w.toMul : G)) (b.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  exact le_inf (inf_le_left.trans (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D))) hU

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
