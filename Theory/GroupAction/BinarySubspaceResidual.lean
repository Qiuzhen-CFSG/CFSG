module
public import Theory.Representation.BinaryFlagPlaneAction
public import Theory.GroupTheory.PResidual.FixedNormalCenter
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Residual fixed points in full binary subspace actions

A full automorphism action on an elementary abelian two-group restricts to
all automorphisms of each subgroup in its setwise stabilizer. For a subgroup
of order greater than two this stabilizer has no nonidentity fixed point.
Its two-residual also has no fixed point: a nontrivial residual-fixed normal
two-subgroup would contain a point in the center of the whole stabilizer.

The extension uses the actual subgroup inclusion and automorphism maps.
Source application: Aschbacher--Smith, 12.2.25, printed pp.805--806, the
fixed-space identity for the residual of the hyperplane normalizer.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinarySubspaceResidual
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

omit [Finite E] in
theorem exists_automorphism (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul x) hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul y) hy
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨BinaryFixedLine.linearAutEquiv.symm g, ?_⟩
  have hh := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
  have hxy : g (Additive.ofMul x) = Additive.ofMul y := by
    have hex : (ex 1 : Additive E) = Additive.ofMul x := congrArg Subtype.val
      (LinearEquiv.toSpanNonzeroSingleton_one (ZMod 2) (Additive E) (Additive.ofMul x) hx)
    have hey : (ey 1 : Additive E) = Additive.ofMul y := congrArg Subtype.val
      (LinearEquiv.toSpanNonzeroSingleton_one (ZMod 2) (Additive E) (Additive.ofMul y) hy)
    rw [hex,hey] at hh
    exact hh.symm
  exact congrArg Additive.toMul hxy

theorem eq_one_of_fixed (hc : 2 < Nat.card E) (x : E)
    (hx : ∀ a : MulAut E, a x = x) : x = 1 := by
  by_contra hn
  have he (y : E) : y = 1 ∨ y = x := by
    by_cases hy : y = 1
    · exact Or.inl hy
    · obtain ⟨a,ha⟩ := exists_automorphism x y hn hy
      exact Or.inr (ha.symm.trans (hx a))
  have hs : (Set.univ : Set E) ⊆ {1,x} := by
    intro y _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he y
  have hh := Set.ncard_le_ncard hs
  have hb : ({1,x} : Set E).ncard ≤ 2 := by simp [Ne.symm hn]
  rw [Set.ncard_univ] at hh
  omega

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Full automorphisms of V induce all automorphisms of each subgroup W in its stabilizer. -/
theorem stabilizer_full (L V W : Subgroup G) [IsElementaryAbelian 2 V]
    (hLV : L ≤ normalizer (V : Set G)) (hWV : W ≤ V)
    (hfull : Function.Surjective (V.normalizerMonoidHom.comp (inclusion hLV))) :
    Function.Surjective (W.normalizerMonoidHom.comp (inclusion
      (show L ⊓ normalizer (W : Set G) ≤ normalizer (W : Set G) from inf_le_right))) := by
  let e := subgroupOfEquivOfLe hWV
  intro a
  let a' : MulAut (W.subgroupOf V) := (e.trans a).trans e.symm
  obtain ⟨b,hb,hbn⟩ := BinaryFlagPlaneAction.exists_extension (W.subgroupOf V) a'
  obtain ⟨l,hl⟩ := hfull b
  have hln : (l : G) ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff.mpr
    intro w
    constructor
    · intro hw
      have hh := (hbn (W.subgroupOf V) le_rfl ⟨w,hWV hw⟩).mpr hw
      rw [←hl] at hh
      exact hh
    · intro hw
      have hwV : w ∈ V := (mem_normalizer_iff.mp (hLV l.property) w).mpr (hWV hw)
      have hh := (hbn (W.subgroupOf V) le_rfl ⟨w,hwV⟩).mp
        (show b ⟨w,hwV⟩ ∈ W.subgroupOf V from by rw [←hl]; exact hw)
      exact hh
  refine ⟨⟨l, l.property,hln⟩, ?_⟩
  ext w
  have hh := hb (e.symm w)
  rw [←hl] at hh
  have hval := congrArg (fun z : V => (z : G)) hh
  simpa [a', e, subgroupOfEquivOfLe] using hval

/-- Full automorphisms on a binary subgroup of order greater than two have no fixed point. -/
theorem fixed_eq_bot (F W : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : F ≤ normalizer (W : Set G)) (hc : 2 < Nat.card W)
    (hfull : Function.Surjective (W.normalizerMonoidHom.comp (inclusion hn))) :
    W ⊓ centralizer (F : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro w hw
  have he : (⟨w,hw.1⟩ : W) = 1 := eq_one_of_fixed hc _ (by
    intro a
    obtain ⟨f,rfl⟩ := hfull a
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hw.2 f f.property))
  exact congrArg Subtype.val he

/-- A residual-fixed normal two-subgroup would contain a point central in F. -/
theorem residual_fixed_eq_bot (F W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWF : W ≤ F) (hn : F ≤ normalizer (W : Set G))
    (hfix : W ⊓ centralizer (F : Set G) = ⊥) :
    W ⊓ centralizer ((pResidual 2 F).map F.subtype : Set G) = ⊥ := by
  let Y := (pResidual 2 F).map F.subtype
  let X := W ⊓ centralizer (Y : Set G)
  have hXF : X ≤ F := inf_le_left.trans hWF
  have hFY : F ≤ normalizer (Y : Set G) :=
    F.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F (pResidual 2 F))
  have hFX : F ≤ normalizer (X : Set G) :=
    (le_inf hn (hFY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  let A := X.subgroupOf F
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hXF).mpr hFX
  have hp : IsPGroup 2 A := ((IsElementaryAbelian.isPGroup 2 W).to_le
    (show X ≤ W from inf_le_left)).comap_subtype
  by_contra hne
  have hAne : A ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map F.subtype) he
    rw [map_subgroupOf_eq_of_le hXF, Subgroup.map_bot] at hh
    exact hne hh
  have hR : pResidual 2 F ≤ centralizer (A : Set F) := by
    intro y hy a ha
    apply Subtype.ext
    exact (ha.2 _ (mem_map_of_mem F.subtype hy)).symm
  let S : Sylow 2 F := Classical.choice inferInstance
  obtain ⟨a,ha,hane,hac⟩ :=
    exists_nontrivial_center_mem_normal_of_residual_centralizes S A hp hAne hR
  have hab : (a : G) ∈ W ⊓ centralizer (F : Set G) := by
    refine ⟨ha.1, ?_⟩
    intro f hf
    exact congrArg Subtype.val ((mem_center_iff.mp hac) ⟨f,hf⟩)
  rw [hfix, mem_bot] at hab
  exact hane (Subtype.ext hab)

end BinarySubspaceResidual
