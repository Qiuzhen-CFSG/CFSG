module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorWeakOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietBinaryThreeGeneration
public import CFSG.Quasithin.ChapterE.Section03.WeakCentralizerContainment
public import Theory.Representation.BinaryTensorThree.PlaneRigidity

/-!
# Zeroth tensor weak closure and rank-one E-generation exclusion

Small-corank fixed-space rigidity first annihilates the action on the plane
radical fixed four-space. Its kernel consists of the paired plane radicals.
The two factor projections have kernels of index at most four; two literal
tensor vectors detect both factors. Rigidity therefore annihilates the whole
action of every conjugate of V lying in T, proving W₀(T,V) ≤ C_T(V).
Source uniqueness now controls N_G(W₀(T,V)). With the ambient C₁ centralizer
bound, rank-one E-generation is impossible for an escaping H-star, so its
already established upper bound gives n(H)=2. The Source consumer supplies
that centralizer bound in the retained Held branch.

Source: Aschbacher--Smith 7.3.3, 8.3.3 and 8.3.9, printed pp.699,723,725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Zeroth weak closure centralizes the original full tensor module. -/
theorem quiet_tensor_weakClosure_zero
    (hs : globalS D.fullModule = 3)
    (q : localJoin T L →* Actor)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hT : ((T : Subgroup G).subgroupOf (localJoin T L)).map q = Matrix.PSL3Two.WreathPair.borel)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v)) :
    indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤
      centralizer (D.fullModule : Set G) := by
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
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hAT⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := hAT.trans le_sup_right
  let f : A →* Line :=
    (q.comp (inclusion hAH)).codRestrict Line (fun a =>
      Matrix.PSL3Two.WreathPair.borel_le_line
        (hT ▸ mem_map_of_mem q (hAT a.property)))
  have hfix (B : Subgroup A) (hB : Nat.log 2 B.index < 3)
      (X : BinaryTensorThree.Space)
      (hX : ∀ x : B, BinaryTensorThree.action
        (BinaryTensorThree.PointParabolic.tensorHom (f x.val).val) X = X)
      (a : A) : BinaryTensorThree.action
        (BinaryTensorThree.PointParabolic.tensorHom (f a).val) X = X := by
    let B' := B.map A.subtype
    have hBA : B' ≤ A := map_subtype_le B
    have hidx : B'.relIndex A = B.index := by
      change (B.map A.subtype).relIndex A = B.index
      rw [relIndex,subgroupOf,comap_map_eq_self_of_injective A.subtype_injective]
    have hcor : (subgroupCorank A B' : ℕ∞) < globalS V := by
      rw [hs]
      apply ENat.natCast_lt_natCast.mpr
      simpa only [subgroupCorank,hidx] using hB
    let v := b.symm X
    have hvB : (v.toMul : G) ∈ V ⊓ centralizer (B' : Set G) := by
      refine ⟨v.toMul.property,?_⟩
      rintro x ⟨x,hx,rfl⟩
      have hh := hX ⟨x,hx⟩
      change BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom
        (q (inclusion hAH x))) X = X at hh
      have hbv : b v = X := b.apply_symm_apply X
      rw [←hbv,←he] at hh
      have hv := congrArg (fun w : Additive V => (w.toMul : G)) (b.injective hh)
      exact mul_inv_eq_iff_eq_mul.mp hv
    have hc := lemma_E_3_7 g (le_inf hBA ((hBA.trans hAH).trans hVN)) hcor
    have hvA : (v.toMul : G) ∈ V ⊓ centralizer (A : Set G) := hc ▸ hvB
    have hcomm := hvA.2 a.val a.property
    have hv : V.normalizerMonoidHom ⟨inclusion hAH a,hVN (hAH a.property)⟩ v.toMul = v.toMul := by
      apply Subtype.ext
      change a.val*(v.toMul : G)*a.val⁻¹ = v.toMul
      rw [hcomm,mul_inv_cancel_right]
    change BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom
      (q (inclusion hAH a))) X = X
    rw [←b.apply_symm_apply X,←he,hv]
    rfl
  have hline := line_action_trivial_of_rigidity f (by
    intro B hB X hX a
    apply Subtype.ext
    exact hfix B (by omega) X.val
      (fun x => congrArg Subtype.val (hX x)) a)
  have hrad (a : A) : (f a).val ∈ radicalPair.range :=
    lineAction_kernel_radical (f a) (Units.ext (hline a))
  have htriv := radical_action_trivial_of_rigidity (Line.subtype.comp f) hrad hfix
  intro a ha v hv
  let a' : A := ⟨a,ha⟩
  let v' : V := ⟨v,hv⟩
  have hh := he (inclusion hAH a') (Additive.ofMul v')
  have hone : q (inclusion hAH a') = 1 := htriv a'
  rw [hone,map_one,map_one] at hh
  have hv' := congrArg (fun w : Additive V => (w.toMul : G)) (b.injective hh)
  exact (mul_inv_eq_iff_eq_mul.mp hv').symm

/-- The original zeroth weak-closure normalizer lies in M, without an
additional positive-w premise. -/
theorem quiet_tensor_weakClosure_zero_normalizer
    (hs : globalS D.fullModule = 3)
    (q : localJoin T L →* Actor)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hT : ((T : Subgroup G).subgroupOf (localJoin T L)).map q = Matrix.PSL3Two.WreathPair.borel)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v)) :
    normalizer (indexedWeakClosure D.fullModule (T : Subgroup G) 0 : Set G) ≤
      D.maximalLocal := by
  apply source_weakClosure_zero_normalizer D
  apply pos_iff_ne_zero.mpr
  intro hz
  have h := globalW_attained (show globalW D.fullModule (T : Subgroup G) = (0 : ℕ) from hz)
  exact h (le_inf (indexedWeakClosure_le _ _ _)
    (quiet_tensor_weakClosure_zero D hs q b hT hb))

/-- The rank-one E-generation exclusion in 8.3.9, retaining precisely the
ambient C₁ centralizer bound supplied by 8.3.8. -/
theorem quiet_tensor_hstar_generation_eq_two
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hs : globalS D.fullModule = 3)
    (q : localJoin T L →* Actor)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hT : ((T : Subgroup G).subgroupOf (localJoin T L)).map q = Matrix.PSL3Two.WreathPair.borel)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v))
    (hC : centralizer (weakCentralizer D.fullModule (T : Subgroup G) 1 : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H = 2 := by
  have hle := quiet_binaryThree_hstar_generation_le_two D hmany hmin hn hJ cL hH
  have hpos := source_hstar_generation_positive D hH
  have hne : generationParameter H ≠ 1 := by
    intro he
    have hgen : IsEGeneratedAt 1 (T.subtype hH.1.1.2) := by
      simpa only [he] using isEGenerated_generationParameter_of_pos hpos (T.subtype hH.1.1.2)
    have hmap : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
        (T : Subgroup G) := map_subgroupOf_eq_of_le hH.1.1.2
    apply hH.1.2
    apply WeakCentralizerContainment.le_of_isEGenerated_one (V := D.fullModule)
      (T.subtype hH.1.1.2) hgen
    · rw [hmap]
      exact quiet_tensor_weakClosure_zero_normalizer D hs q b hT hb
    · rw [hmap]
      exact inf_le_right.trans hC
    · rw [hs]
      decide
  omega

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
