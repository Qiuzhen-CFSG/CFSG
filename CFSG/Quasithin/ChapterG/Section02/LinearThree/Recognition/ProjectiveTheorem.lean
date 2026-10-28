module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Projective recognition for characteristic-two SL₃ modules

This proves the universe-polymorphic implication in `Projective.lean`.
Write Uᵢ for the three coordinate-point images and Δᵢⱼ(a) for the
binary displacement of 1 + aEᵢⱼ. The root clauses give its image and
kernel. A Weyl word interchanges Uᵢ and Uⱼ; disjointness then makes
opposite unit displacements inverse. Elementary generation and projective
transitivity give spanning, and the displacement projections prove that
the three images form a direct sum.

On U₀, the operators Δ₀₁(a)Δ₁₀(1) define the F-action. The commutator
relations through the third coordinate prove multiplicativity. An F-basis
of U₀ supplies the multiplicity and binary coordinates for the whole
module. Every elementary matrix intertwines these coordinates, so their
generation theorem supplies equivariance for all of SL₃. Finally the
actual natural marking transports this equivalence to the original actor
and vector space. No semisimplicity or recognition premise is assumed.

The argument in dimension three needs no lower bound on the field size;
in particular it covers the required nonbinary case. Zero point images
are allowed throughout. The G.2.5 application is in `RecognizedModels`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1–3
and G.1.8–11, printed pp.327–331, PDF pp.338–342. Elementary generation
uses the existing attributed ATLAS port.
-/

public section
noncomputable section

open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
variable {F : Type*} [Field F]

private def framePoint (i : Fin 3) : Point F (Fin 3 → F) :=
  ⟨Submodule.span F {Pi.single i 1}, finrank_span_singleton (by
    intro h
    have := congrFun h i
    simp at this)⟩

private def frameAxis (j : Fin 3) : Submodule F (Fin 3 → F) :=
  LinearMap.ker (LinearMap.proj j)

private lemma frameAxis_dimension (j : Fin 3) :
    Module.finrank F (frameAxis (F := F) j) + 1 =
      Module.finrank F (Fin 3 → F) := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro he
  have := LinearMap.congr_fun he (Pi.single j 1)
  simp at this

private lemma framePoint_le_axis {i j : Fin 3} (hij : i ≠ j) :
    (framePoint (F := F) i).val ≤ frameAxis j := by
  apply Submodule.span_le.mpr
  rintro _ rfl
  change (Pi.single i (1 : F) : Fin 3 → F) j = 0
  exact Pi.single_eq_of_ne hij.symm _

private lemma framePoint_ne {i j : Fin 3} (hij : i ≠ j) :
    framePoint (F := F) i ≠ framePoint j := by
  intro he
  have hv : Pi.single i (1 : F) ∈ (framePoint (F := F) j).val :=
    congrArg Subtype.val he ▸ Submodule.subset_span (Set.mem_singleton _)
  have hz := framePoint_le_axis (F := F) hij.symm hv
  change (Pi.single i (1 : F) : Fin 3 → F) i = 0 at hz
  simp at hz

private lemma frameRoot_action {i j : Fin 3} (hij : i ≠ j) (a : F) (v : Fin 3 → F) :
    Representation.specialLinearNatural 3 (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single i (a * v j) := by
  simp [Representation.specialLinearNatural_apply, SpecialLinearGroup.transvection_coe,
    add_mulVec, single_mulVec_eq, ← Pi.single_smul]

private lemma frameRoot_mem {i j : Fin 3} (hij : i ≠ j) (a : F) :
    SpecialLinearGroup.transvection hij a ∈
      rootGroup (Representation.specialLinearNatural 3)
        (framePoint (F := F) i).val (frameAxis j) := by
  constructor
  · intro v
    rw [frameRoot_action, add_sub_cancel_left]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a * v j, ?_⟩
    ext k
    by_cases hk : k = i
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  · intro v hv
    change v j = 0 at hv
    rw [frameRoot_action, hv]
    simp

private lemma framePoint_transitive (A : Point F (Fin 3 → F)) :
    ∃ g : SL(3,F), (framePoint (F := F) 0).val.map
      (Representation.specialLinearNatural 3 g) = A.val := by
  obtain ⟨v, hv, hv0⟩ := A.val.ne_bot_iff.mp
    (Submodule.isAtom_iff_finrank_eq_one.mpr A.property).ne_bot
  obtain ⟨g, hg⟩ := SpecialLinearGroup.exists_mulVec_eq_three
    (Pi.single 0 1) v (by intro he; have := congrFun he 0; simp at this) hv0
  refine ⟨g, ?_⟩
  change (Submodule.span F {Pi.single 0 1}).map _ = _
  rw [eq_span_singleton_of_mem_of_finrank_eq_one A.property hv hv0,
    Submodule.map_span, Set.image_singleton]
  exact congrArg (fun w => Submodule.span F {w}) hg

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
variable {ρ : Representation (ZMod 2) SL(3,F) M}
  {φ : Point F (Fin 3 → F) → Submodule (ZMod 2) M}
  (hc : Criterion (Representation.specialLinearNatural 3) ρ φ)

include hc

private lemma Criterion.frame_moved {i j : Fin 3} (hij : i ≠ j) (a : F) (v : M) :
    ρ (SpecialLinearGroup.transvection hij a) v - v ∈ φ (framePoint i) :=
  hc.root_moved _ _ (frameAxis_dimension j) (framePoint_le_axis hij)
    _ (frameRoot_mem hij a) v

private lemma Criterion.frame_fixed {i j : Fin 3} (hij : i ≠ j)
    (k : Fin 3) (hkj : k ≠ j) (a : F) (v : M) (hv : v ∈ φ (framePoint k)) :
    ρ (SpecialLinearGroup.transvection hij a) v = v :=
  hc.root_fixed _ _ (frameAxis_dimension j) (framePoint_le_axis hij)
    _ (framePoint_le_axis hkj) _ (frameRoot_mem hij a) v hv

private lemma Criterion.frame_spanning : (⨆ i, φ (framePoint i)) = ⊤ := by
  let N := ⨆ i, φ (framePoint i)
  have hstable (g : SL(3,F)) : ∀ v ∈ N, ρ g v ∈ N := by
    apply Atlas.sl_elementary_induction (fun g => ∀ v ∈ N, ρ g v ∈ N) ?_ ?_ g
    · intro i j hij a v hv
      have hd : ρ (SpecialLinearGroup.transvection hij a) v - v ∈ N :=
        (le_iSup (fun i => φ (framePoint i)) i) (hc.frame_moved hij a v)
      simpa only [sub_add_cancel] using N.add_mem hd hv
    · intro a b ha hb v hv
      rw [map_mul, Module.End.mul_apply]
      exact ha _ (hb _ hv)
  apply top_unique
  rw [← hc.spanning]
  apply iSup_le
  intro A
  obtain ⟨g, hg⟩ := framePoint_transitive A
  rw [hc.equivariant g (framePoint 0) A hg.symm]
  rintro _ ⟨v, hv, rfl⟩
  exact hstable g v ((le_iSup (fun i => φ (framePoint i)) 0) hv)

variable [CharP F 2]
omit hc in
private lemma frameSwap_map {i j : Fin 3} (hij : i ≠ j) :
    (framePoint (F := F) i).val.map (Representation.specialLinearNatural 3
      (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij.symm 1 *
        SpecialLinearGroup.transvection hij 1)) = (framePoint j).val := by
  change (Submodule.span F {Pi.single i 1}).map _ = Submodule.span F {Pi.single j 1}
  rw [Submodule.map_span, Set.image_singleton]
  apply congrArg (fun v => Submodule.span F {v})
  simp only [map_mul, Module.End.mul_apply, frameRoot_action]
  simp only [Pi.single_eq_of_ne hij.symm,
    Pi.single_eq_same, mul_zero, Pi.single_zero, add_zero,
    Pi.add_apply, Pi.zero_apply, zero_add, one_mul]
  rw [add_right_comm]
  have hz : (Pi.single i (1 : F) : Fin 3 → F) + Pi.single i 1 = 0 := by
    ext k
    exact CharTwo.add_self_eq_zero _
  rw [hz, zero_add]

omit [Field F] hc [CharP F 2] in
private lemma binary_add_self (v : M) : v + v = 0 := by
  simpa only [one_smul, show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul] using
    (add_smul (1 : ZMod 2) 1 v).symm

private def Criterion.rootMap {i j : Fin 3} (hij : i ≠ j) (a : F) :
    φ (framePoint j) →ₗ[ZMod 2] φ (framePoint i) :=
  ((ρ (SpecialLinearGroup.transvection hij a) - 1).comp
    (φ (framePoint j)).subtype).codRestrict _ (fun v => hc.frame_moved hij a v)

omit [CharP F 2] in
private lemma Criterion.rootMap_val {i j : Fin 3} (hij : i ≠ j) (a : F)
    (v : φ (framePoint j)) :
    (hc.rootMap hij a v : M) = ρ (SpecialLinearGroup.transvection hij a) v - v := rfl

private lemma Criterion.rootMap_inverse {i j : Fin 3} (hij : i ≠ j)
    (v : φ (framePoint i)) : hc.rootMap hij 1 (hc.rootMap hij.symm 1 v) = v := by
  let x := SpecialLinearGroup.transvection hij (1 : F)
  let y := SpecialLinearGroup.transvection hij.symm (1 : F)
  let w := x * y * x
  have hw : ρ w (v : M) ∈ φ (framePoint j) := by
    rw [hc.equivariant w (framePoint i) (framePoint j) (frameSwap_map hij).symm]
    exact ⟨v, v.property, rfl⟩
  have hx : ρ x (v : M) = v := hc.frame_fixed hij i hij 1 v v.property
  let b := hc.rootMap hij.symm 1 v
  let c := hc.rootMap hij 1 b
  have he : ρ w (v : M) = (v : M) + b + c := by
    change ρ (x * y * x) (v : M) = (v : M) +
      (ρ y v - v) + (ρ x (ρ y v - v) - (ρ y v - v))
    simp only [map_mul, Module.End.mul_apply, map_sub, hx]
    abel
  have hj : (v : M) + c ∈ φ (framePoint j) := by
    have ht := (φ (framePoint j)).sub_mem hw b.property
    rw [he] at ht
    convert ht using 1
    abel
  have hi := (φ (framePoint i)).add_mem v.property c.property
  have hz : (v : M) + c = 0 :=
    (Submodule.disjoint_def.mp (hc.disjoint _ _ (framePoint_ne hij))) _ hi hj
  apply Subtype.ext
  change (c : M) = v
  calc
    (c : M) = (v : M) + ((v : M) + c) := by rw [← add_assoc, binary_add_self, zero_add]
    _ = v := by rw [hz, add_zero]

omit [CharP F 2] in
private lemma Criterion.rootMap_add {i j : Fin 3} (hij : i ≠ j) (a b : F) :
    hc.rootMap hij (a + b) = hc.rootMap hij a + hc.rootMap hij b := by
  ext v
  have hf := hc.frame_fixed hij i hij a _ (hc.frame_moved hij b v)
  simp only [map_sub] at hf
  simp only [rootMap_val, LinearMap.add_apply, Submodule.coe_add,
    SpecialLinearGroup.transvection_add, map_mul, Module.End.mul_apply]
  rw [sub_eq_iff_eq_add] at hf
  rw [hf]
  abel

omit hc [CharP F 2] in
private lemma frameRoot_chain {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : F) :
    SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hjk b =
      SpecialLinearGroup.transvection hik (a * b) *
        SpecialLinearGroup.transvection hjk b * SpecialLinearGroup.transvection hij a := by
  apply Subtype.ext
  change ((1 : Matrix (Fin 3) (Fin 3) F) + single i j a) * (1 + single j k b) =
    (1 + single i k (a * b)) * (1 + single j k b) * (1 + single i j a)
  simp only [mul_add, add_mul, one_mul, mul_one, add_zero, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hjk.symm,
    single_mul_single_of_ne _ _ _ _ hik.symm]
  abel

omit [CharP F 2] in
private lemma Criterion.rootMap_chain {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) (v : φ (framePoint k)) :
    hc.rootMap hij a (hc.rootMap hjk b v) = hc.rootMap hik (a * b) v := by
  have he := congrArg (fun g => ρ g (v : M)) (frameRoot_chain hij hjk hik a b)
  have hix := hc.frame_fixed hij k hjk.symm a v v.property
  have hiz := hc.frame_fixed hik j hjk (a * b) _ (hc.frame_moved hjk b v)
  simp only [map_sub] at hiz
  simp only [map_mul, Module.End.mul_apply, hix] at he
  apply Subtype.ext
  simp only [rootMap_val, map_sub, hix]
  rw [he]
  rw [sub_eq_iff_eq_add] at hiz
  rw [hiz]
  abel

private def Criterion.rootEquiv {i j : Fin 3} (hij : i ≠ j) :
    φ (framePoint j) ≃ₗ[ZMod 2] φ (framePoint i) :=
  { hc.rootMap hij 1 with
    invFun := hc.rootMap hij.symm 1
    left_inv := hc.rootMap_inverse hij.symm
    right_inv := hc.rootMap_inverse hij }

private def Criterion.coefficient (a : F) : Module.End (ZMod 2) (φ (framePoint 0)) :=
  (hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) a).comp
    (hc.rootMap (show (1 : Fin 3) ≠ 0 by decide) 1)

omit [CharP F 2] in
private lemma Criterion.coefficient_alt (a : F) (v : φ (framePoint 0)) :
    hc.coefficient a v =
      hc.rootMap (show (0 : Fin 3) ≠ 2 by decide) a
        (hc.rootMap (show (2 : Fin 3) ≠ 0 by decide) 1 v) := by
  change hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) a
    (hc.rootMap (show (1 : Fin 3) ≠ 0 by decide) 1 v) = _
  have ht := hc.rootMap_chain (show (1 : Fin 3) ≠ 2 by decide)
    (show (2 : Fin 3) ≠ 0 by decide) (by decide) 1 1 v
  rw [mul_one] at ht
  rw [← ht]
  simpa only [mul_one] using hc.rootMap_chain (show (0 : Fin 3) ≠ 1 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) (by decide) a 1
      (hc.rootMap (show (2 : Fin 3) ≠ 0 by decide) 1 v)

omit [CharP F 2] in
private lemma Criterion.coefficient_mul (a b : F) :
    hc.coefficient (a * b) = hc.coefficient a * hc.coefficient b := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, hc.coefficient_alt a]
  change _ = hc.rootMap (show (0 : Fin 3) ≠ 2 by decide) a
    (hc.rootMap (show (2 : Fin 3) ≠ 0 by decide) 1
      (hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) b
        (hc.rootMap (show (1 : Fin 3) ≠ 0 by decide) 1 v)))
  rw [hc.rootMap_chain (show (2 : Fin 3) ≠ 0 by decide)
    (show (0 : Fin 3) ≠ 1 by decide) (by decide), one_mul]
  rw [hc.rootMap_chain (show (0 : Fin 3) ≠ 2 by decide)
    (show (2 : Fin 3) ≠ 1 by decide) (by decide)]
  rfl

private def Criterion.coefficientHom : F →+* Module.End (ZMod 2) (φ (framePoint 0)) where
  toFun := hc.coefficient
  map_one' := by
    apply LinearMap.ext
    intro v
    exact hc.rootMap_inverse (show (0 : Fin 3) ≠ 1 by decide) v
  map_mul' := hc.coefficient_mul
  map_zero' := by
    ext v
    simp [coefficient, rootMap, SpecialLinearGroup.transvection_coeff_zero]
  map_add' a b := by
    simp only [coefficient, hc.rootMap_add, LinearMap.add_comp]

private def Criterion.toFirst (i : Fin 3) :
    φ (framePoint i) ≃ₗ[ZMod 2] φ (framePoint 0) :=
  if hi : i = 0 then
    LinearEquiv.ofEq _ _ (congrArg (fun j => φ (framePoint j)) hi)
  else hc.rootEquiv (Ne.symm hi)

private lemma Criterion.toFirst_zero : hc.toFirst 0 = LinearEquiv.refl _ _ := by
  simp [toFirst]

private lemma Criterion.toFirst_ne {i : Fin 3} (hi : i ≠ 0) (v : φ (framePoint i)) :
    hc.toFirst i v = hc.rootMap hi.symm 1 v := by
  simp [toFirst, hi, rootEquiv]

private lemma Criterion.coefficient_root_one (a : F) (v : φ (framePoint 1)) :
    hc.coefficient a (hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) 1 v) =
      hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) a v := by
  change hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) a
    (hc.rootMap (show (1 : Fin 3) ≠ 0 by decide) 1
      (hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) 1 v)) = _
  rw [hc.rootMap_inverse]

private lemma Criterion.coefficient_root_two (a : F) (v : φ (framePoint 2)) :
    hc.coefficient a (hc.rootMap (show (0 : Fin 3) ≠ 2 by decide) 1 v) =
      hc.rootMap (show (0 : Fin 3) ≠ 2 by decide) a v := by
  rw [hc.coefficient_alt, hc.rootMap_inverse]

omit [CharP F 2] in
private lemma Criterion.loop_one (a : F) (v : φ (framePoint 0)) :
    hc.rootMap (show (0 : Fin 3) ≠ 1 by decide) 1
      (hc.rootMap (show (1 : Fin 3) ≠ 0 by decide) a v) = hc.coefficient a v := by
  have ht := hc.rootMap_chain (show (1 : Fin 3) ≠ 2 by decide)
    (show (2 : Fin 3) ≠ 0 by decide) (by decide) a 1 v
  rw [mul_one] at ht
  rw [← ht]
  rw [hc.rootMap_chain (show (0 : Fin 3) ≠ 1 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) (by decide), one_mul]
  exact (hc.coefficient_alt a v).symm

omit [CharP F 2] in
private lemma Criterion.loop_two (a : F) (v : φ (framePoint 0)) :
    hc.rootMap (show (0 : Fin 3) ≠ 2 by decide) 1
      (hc.rootMap (show (2 : Fin 3) ≠ 0 by decide) a v) = hc.coefficient a v := by
  have ht := hc.rootMap_chain (show (2 : Fin 3) ≠ 1 by decide)
    (show (1 : Fin 3) ≠ 0 by decide) (by decide) a 1 v
  rw [mul_one] at ht
  rw [← ht]
  rw [hc.rootMap_chain (show (0 : Fin 3) ≠ 2 by decide)
    (show (2 : Fin 3) ≠ 1 by decide) (by decide), one_mul]
  rfl

private lemma Criterion.toFirst_root {i j : Fin 3} (hij : i ≠ j) (a : F)
    (v : φ (framePoint j)) :
    hc.toFirst i (hc.rootMap hij a v) = hc.coefficient a (hc.toFirst j v) := by
  fin_cases i <;> fin_cases j
  all_goals dsimp only at *
  all_goals try exact (hij rfl).elim
  · exact (hc.coefficient_root_one a v).symm
  · exact (hc.coefficient_root_two a v).symm
  · exact hc.loop_one a v
  · rw [hc.toFirst_ne (by decide), hc.toFirst_ne (by decide),
      hc.rootMap_chain (show (0 : Fin 3) ≠ 1 by decide)
        (show (1 : Fin 3) ≠ 2 by decide) (by decide), one_mul]
    exact (hc.coefficient_root_two a v).symm
  · exact hc.loop_two a v
  · rw [hc.toFirst_ne (by decide), hc.toFirst_ne (by decide),
      hc.rootMap_chain (show (0 : Fin 3) ≠ 2 by decide)
        (show (2 : Fin 3) ≠ 1 by decide) (by decide), one_mul]
    exact (hc.coefficient_root_one a v).symm

private def frameSum (φ : Point F (Fin 3 → F) → Submodule (ZMod 2) M) :
    ((i : Fin 3) → φ (framePoint i)) →ₗ[ZMod 2] M :=
  LinearMap.lsum (ZMod 2) (fun i => φ (framePoint i)) (ZMod 2)
    (fun i => (φ (framePoint i)).subtype)

omit hc [CharP F 2] in
private lemma frameSum_apply (v : (i : Fin 3) → φ (framePoint i)) :
    frameSum φ v = ∑ i, (v i : M) := by
  simp [frameSum, LinearMap.lsum_apply, LinearMap.sum_apply]

omit hc [CharP F 2] in
private lemma frameSum_single (i : Fin 3) (v : φ (framePoint i)) :
    frameSum φ (Pi.single i v) = (v : M) :=
  LinearMap.lsum_piSingle (ZMod 2) (fun i : Fin 3 => φ (framePoint i)) (ZMod 2)
    (fun i => (φ (framePoint i)).subtype) i v

omit [CharP F 2] in
private lemma Criterion.frameSum_surjective : Function.Surjective (frameSum φ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hc.frame_spanning]
  refine iSup_le fun i v hv => ?_
  exact ⟨Pi.single i ⟨v, hv⟩, frameSum_single i ⟨v, hv⟩⟩

private lemma Criterion.frameSum_injective : Function.Injective (frameSum φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [frameSum_apply] at hv
  funext i
  obtain ⟨j, hji⟩ := exists_ne i
  let d : Module.End (ZMod 2) M := ρ (SpecialLinearGroup.transvection hji (1 : F)) - 1
  have he := congrArg d hv
  rw [map_sum, map_zero] at he
  have hs : ∑ k, d (v k : M) = d (v i : M) := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      change ρ (SpecialLinearGroup.transvection hji (1 : F)) (v k) - v k = 0
      rw [hc.frame_fixed hji k hki 1 (v k) (v k).property, sub_self]
    · simp
  rw [hs] at he
  have hz : hc.rootMap hji 1 (v i) = 0 := Subtype.ext he
  have hi := congrArg (hc.rootMap hji.symm 1) hz
  change v i = 0
  simpa only [hc.rootMap_inverse hji.symm, map_zero] using hi

private def Criterion.frameCoordinates :
    M ≃ₗ[ZMod 2] ((i : Fin 3) → φ (framePoint i)) :=
  (LinearEquiv.ofBijective (frameSum φ)
    ⟨hc.frameSum_injective, hc.frameSum_surjective⟩).symm

private lemma Criterion.frameCoordinates_sum (v : M) :
    ∑ i, (hc.frameCoordinates v i : M) = v := by
  exact (hc.frameCoordinates).symm_apply_apply v

private lemma Criterion.frameCoordinates_single (i : Fin 3) (v : φ (framePoint i)) :
    hc.frameCoordinates (v : M) = Pi.single i v := by
  apply hc.frameCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (frameSum_single i v).symm

private lemma Criterion.frameCoordinates_root {i j : Fin 3} (hij : i ≠ j) (a : F) (v : M) :
    hc.frameCoordinates (ρ (SpecialLinearGroup.transvection hij a) v) =
      hc.frameCoordinates v + Pi.single i (hc.rootMap hij a (hc.frameCoordinates v j)) := by
  let d : Module.End (ZMod 2) M := ρ (SpecialLinearGroup.transvection hij a) - 1
  have hd : d v = (hc.rootMap hij a (hc.frameCoordinates v j) : M) := by
    calc
      d v = d (∑ k, (hc.frameCoordinates v k : M)) :=
        congrArg d (hc.frameCoordinates_sum v).symm
      _ = ∑ k, d (hc.frameCoordinates v k : M) := map_sum d _ _
      _ = d (hc.frameCoordinates v j : M) := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          change ρ (SpecialLinearGroup.transvection hij a) (hc.frameCoordinates v k) -
            hc.frameCoordinates v k = 0
          rw [hc.frame_fixed hij k hkj a _ (hc.frameCoordinates v k).property, sub_self]
        · simp
      _ = _ := rfl
  have he : ρ (SpecialLinearGroup.transvection hij a) v =
      v + (hc.rootMap hij a (hc.frameCoordinates v j) : M) := by
    rw [← hd]
    change ρ _ v = v + (ρ _ v - v)
    abel
  rw [he, map_add, hc.frameCoordinates_single]

private def Criterion.firstCoordinates :
    M ≃ₗ[ZMod 2] (Fin 3 → φ (framePoint 0)) :=
  hc.frameCoordinates.trans (LinearEquiv.piCongrRight hc.toFirst)

private lemma Criterion.firstCoordinates_apply (v : M) (i : Fin 3) :
    hc.firstCoordinates v i = hc.toFirst i (hc.frameCoordinates v i) := rfl

private lemma Criterion.firstCoordinates_root {i j : Fin 3} (hij : i ≠ j) (a : F) (v : M) :
    hc.firstCoordinates (ρ (SpecialLinearGroup.transvection hij a) v) =
      hc.firstCoordinates v + Pi.single i (hc.coefficient a (hc.firstCoordinates v j)) := by
  funext k
  simp only [firstCoordinates_apply, hc.frameCoordinates_root, Pi.add_apply, map_add]
  by_cases hki : k = i
  · subst k
    simp only [Pi.single_eq_same, hc.toFirst_root]
  · simp only [Pi.single_eq_of_ne hki, map_zero, add_zero]

attribute [local instance] ZMod.algebra

private lemma Criterion.coefficient_coordinates [Finite M] :
    ∃ r : ℕ, ∃ e : φ (framePoint 0) ≃ₗ[ZMod 2] (Fin r → F),
      ∀ a v i, e (hc.coefficient a v) i = a * e v i := by
  let : Module F (φ (framePoint 0)) := Module.compHom _ hc.coefficientHom
  let e := (Module.finBasis F (φ (framePoint 0))).equivFun
  refine ⟨Module.finrank F (φ (framePoint 0)), e.restrictScalars (ZMod 2), ?_⟩
  intro a v i
  have he := congrFun (e.map_smul a v) i
  exact he

private def coefficientPiEquiv {r : ℕ}
    (e : φ (framePoint 0) ≃ₗ[ZMod 2] (Fin r → F)) :
    (Fin 3 → φ (framePoint 0)) ≃ₗ[ZMod 2] (Fin r → Fin 3 → F) where
  toFun v i j := e (v j) i
  invFun v j := e.symm (fun i => v i j)
  left_inv v := by funext j; exact e.symm_apply_apply (v j)
  right_inv v := by funext i j; exact congrFun (e.apply_symm_apply (fun k => v k j)) i
  map_add' v w := by
    funext i j
    exact congrFun (e.map_add (v j) (w j)) i
  map_smul' a v := by
    funext i j
    exact congrFun (e.map_smul a (v j)) i

private lemma Criterion.standard_recognition [Finite M] :
    ∃ r : ℕ, Homogeneous (Representation.specialLinearNatural 3) ρ r := by
  obtain ⟨r, e, he⟩ := hc.coefficient_coordinates
  let E := hc.firstCoordinates.trans (coefficientPiEquiv e)
  refine ⟨r, E, ?_⟩
  intro g
  apply Atlas.sl_elementary_induction
    (fun g => ∀ v i, E (ρ g v) i = Representation.specialLinearNatural 3 g (E v i))
    ?_ ?_ g
  · intro j k hjk a v i
    change (fun l => e (hc.firstCoordinates (ρ _ v) l) i) = _
    rw [hc.firstCoordinates_root, frameRoot_action]
    funext l
    change e (hc.firstCoordinates v l + (Pi.single j _ : Fin 3 → φ (framePoint 0)) l) i =
      e (hc.firstCoordinates v l) i +
        (Pi.single j (a * e (hc.firstCoordinates v k) i) : Fin 3 → F) l
    rw [map_add, Pi.add_apply]
    by_cases hlj : l = j
    · subst l
      simp only [Pi.single_eq_same, he]
    · simp only [Pi.single_eq_of_ne hlj, map_zero, Pi.zero_apply]
  · intro a b ha hb v i
    rw [map_mul, Module.End.mul_apply, ha, hb, map_mul, Module.End.mul_apply]

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
universe uF uK uV uM
variable {F : Type uF} [Field F]
variable {V : Type uV} [AddCommGroup V] [Module F V]

private def pointEquiv {W : Type*} [AddCommGroup W] [Module F W] (e : V ≃ₗ[F] W) :
    Point F V ≃ Point F W where
  toFun A := ⟨A.val.map e.toLinearMap, (e.finrank_map_eq A.val).trans A.property⟩
  invFun A := ⟨A.val.map e.symm.toLinearMap, (e.symm.finrank_map_eq A.val).trans A.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.map e.toLinearMap).map e.symm.toLinearMap = A.val
    rw [← Submodule.map_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext v; exact e.symm_apply_apply v
    rw [he, Submodule.map_id]
  right_inv A := by
    apply Subtype.ext
    change (A.val.map e.symm.toLinearMap).map e.toLinearMap = A.val
    rw [← Submodule.map_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext v; exact e.apply_symm_apply v
    rw [he, Submodule.map_id]

variable {K : Type uK} [Group K] {γ : Representation F K V}
    (d : NaturalMarking γ)

private lemma NaturalMarking.inverse_action (g : Matrix.SpecialLinearGroup (Fin 3) F)
    (v : Fin 3 → F) :
    γ (d.groupEquiv.symm g) (d.coordinates.symm v) =
      d.coordinates.symm (Representation.specialLinearNatural 3 g v) := by
  apply d.coordinates.injective
  rw [d.equivariant, d.groupEquiv.apply_symm_apply,
    d.coordinates.apply_symm_apply, d.coordinates.apply_symm_apply]

private lemma NaturalMarking.root_mem (A B : Submodule F (Fin 3 → F))
    (g : Matrix.SpecialLinearGroup (Fin 3) F)
    (hg : g ∈ rootGroup (Representation.specialLinearNatural 3) A B) :
    d.groupEquiv.symm g ∈ rootGroup γ
      (A.map d.coordinates.symm.toLinearMap) (B.map d.coordinates.symm.toLinearMap) := by
  constructor
  · intro v
    refine ⟨Representation.specialLinearNatural 3 g (d.coordinates v) - d.coordinates v,
      hg.1 (d.coordinates v), ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub, ← d.inverse_action,
      d.coordinates.symm_apply_apply]
  · rintro _ ⟨v, hv, rfl⟩
    change γ (d.groupEquiv.symm g) (d.coordinates.symm v) = d.coordinates.symm v
    rw [d.inverse_action, hg.2 v hv]

variable {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) K M}
    {φ : Point F V → Submodule (ZMod 2) M}

private lemma Criterion.marked_transport (hc : Criterion γ ρ φ) :
    Criterion (Representation.specialLinearNatural 3)
      (ρ.comp d.groupEquiv.symm.toMonoidHom)
      (fun A => φ (pointEquiv d.coordinates.symm A)) := by
  constructor
  · intro g A B hAB
    apply hc.equivariant (d.groupEquiv.symm g)
    change B.val.map d.coordinates.symm.toLinearMap =
      (A.val.map d.coordinates.symm.toLinearMap).map (γ (d.groupEquiv.symm g))
    rw [hAB, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro v
    exact (d.inverse_action g v).symm
  · intro A B hdim hAB g hg v
    apply hc.root_moved (pointEquiv d.coordinates.symm A)
      (B.map d.coordinates.symm.toLinearMap) ?_ (Submodule.map_mono hAB)
      (d.groupEquiv.symm g) (d.root_mem A.val B g hg) v
    rw [d.coordinates.symm.finrank_map_eq, d.coordinates.finrank_eq]
    exact hdim
  · intro A B hdim hAB D hDB g hg v hv
    apply hc.root_fixed (pointEquiv d.coordinates.symm A)
      (B.map d.coordinates.symm.toLinearMap) ?_ (Submodule.map_mono hAB)
      (pointEquiv d.coordinates.symm D) (Submodule.map_mono hDB)
      (d.groupEquiv.symm g) (d.root_mem A.val B g hg) v hv
    rw [d.coordinates.symm.finrank_map_eq, d.coordinates.finrank_eq]
    exact hdim
  · intro A B hAB
    exact hc.disjoint _ _ ((pointEquiv d.coordinates.symm).injective.ne hAB)
  · rw [Equiv.iSup_comp (pointEquiv d.coordinates.symm)]
    exact hc.spanning

attribute [local instance] ZMod.algebra

/-- The three-dimensional G.1.3 implication, for every actual natural marking.
The construction permits zero point images and multiplicity zero. -/
theorem recognitionImplication [Finite F] [CharP F 2] :
    RecognitionImplication.{uF, uK, uV, uM} F := by
  intro K _ V _ _ _ γ d M _ _ _ ρ φ hc
  obtain ⟨r, e, he⟩ := (hc.marked_transport d).standard_recognition
  let c : (Fin 3 → F) ≃ₗ[ZMod 2] V :=
    { d.coordinates.symm.toAddEquiv with
      map_smul' := fun a v => ZMod.map_smul d.coordinates.symm a v }
  let E : M ≃ₗ[ZMod 2] (Fin r → V) := e.trans (LinearEquiv.piCongrRight (fun _ => c))
  refine ⟨r, E, ?_⟩
  intro g v i
  change d.coordinates.symm (e (ρ g v) i) = γ g (d.coordinates.symm (e v i))
  have h := he (d.groupEquiv g) v i
  change e (ρ (d.groupEquiv.symm (d.groupEquiv g)) v) i =
    Representation.specialLinearNatural 3 (d.groupEquiv g) (e v i) at h
  rw [d.groupEquiv.symm_apply_apply] at h
  rw [h]
  exact (d.inverse_action (d.groupEquiv g) (e v i)).symm.trans (by
    rw [d.groupEquiv.symm_apply_apply])

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
