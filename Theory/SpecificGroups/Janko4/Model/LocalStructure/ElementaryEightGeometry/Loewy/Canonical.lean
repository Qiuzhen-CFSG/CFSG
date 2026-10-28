module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Isotropic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Canonical displacement layers for the native elementary eight

The original 112-dimensional row action defines successive commutator layers.
Every element of the whole ambient normalizer preserves each layer, and
conjugation preserves whether a single element's displacement fills the next
layer. The eight actual kernel and lift generators compute those layers.

For the native (b) eight, `nativeDefectSet` is the concrete set where displacement
from layer three fails to fill layer four. Its whole-normalizer invariance is
proved here. Identifying that set with `isotropicSubgroup` still requires the
native layer and finite image certificates; no such equality is assumed.
This supplies the structural part of the representation route to
Kleidman--Wilson (1988), Corollary 2.3.6, printed p.493.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Subgroup Matrix
open scoped Matrix
attribute [local irreducible] modelGroup matrixA matrixB
abbrev V := Fin 112 → ZMod 2

/-- The original row action, with no change of source matrix convention. -/
def rowAction (g : Model) : V ≃ₗ[ZMod 2] V where
  toFun v := v ᵥ* toMatrix g
  invFun v := v ᵥ* toMatrix g⁻¹
  left_inv v := by dsimp only; rw [vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, vecMul_one]
  right_inv v := by dsimp only; rw [vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one, vecMul_one]
  map_add' v w := add_vecMul _ _ _
  map_smul' a v := by simp only [smul_vecMul, RingHom.id_apply]

@[simp] theorem rowAction_apply (g : Model) (v : V) : rowAction g v = v ᵥ* toMatrix g := rfl

theorem rowAction_mul (g h : Model) (v : V) : rowAction (g*h) v = rowAction h (rowAction g v) := by
  simp only [rowAction_apply,map_mul,vecMul_vecMul]

def displacement (x : Model) : V →ₗ[ZMod 2] V := (rowAction x).toLinearMap - LinearMap.id

theorem displacement_apply (x : Model) (v : V) : displacement x v = rowAction x v - v := rfl

def moved (W : Submodule (ZMod 2) V) (C : Subgroup Model) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ x ∈ C, ∃ w ∈ W, displacement x w = v}

def layer (C : Subgroup Model) : ℕ → Submodule (ZMod 2) V
  | 0 => ⊤
  | n+1 => moved (layer C n) C

theorem rowAction_displacement (g x : Model) (v : V) :
    rowAction g (displacement x v) =
      displacement (g⁻¹*x*g) (rowAction g v) := by
  have he : x*g = g*(g⁻¹*x*g) := by group
  simp only [displacement_apply,map_sub,← rowAction_mul,he]

theorem layer_stable (C : Subgroup Model) (n : ℕ) (g : Model)
    (hg : g ∈ normalizer (C : Set Model)) (v : V) (hv : v ∈ layer C n) :
    rowAction g v ∈ layer C n := by
  induction n generalizing v with
  | zero => trivial
  | succ n ih =>
    apply Submodule.span_induction (p := fun v _ => rowAction g v ∈ layer C (n+1)) _ _ _ _ hv
    · rintro v ⟨x,hx,w,hw,rfl⟩
      rw [rowAction_displacement]
      apply Submodule.subset_span
      exact ⟨g⁻¹*x*g, by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hg) x).mp hx,
        rowAction g w, ih w hw, rfl⟩
    · simpa only [map_zero] using (layer C (n+1)).zero_mem
    · intro a b _ _ ha hb
      simpa only [map_add] using (layer C (n+1)).add_mem ha hb
    · intro a b _ hb
      simpa only [map_smul] using (layer C (n+1)).smul_mem a hb

theorem layer_map (C : Subgroup Model) (n : ℕ) (g : Model)
    (hg : g ∈ normalizer (C : Set Model)) :
    (layer C n).map (rowAction g).toLinearMap = layer C n := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact layer_stable C n g hg v hv
  · intro v hv
    refine ⟨rowAction g⁻¹ v, layer_stable C n g⁻¹ ((normalizer _).inv_mem hg) v hv, ?_⟩
    change rowAction g (rowAction g⁻¹ v) = v
    rw [← rowAction_mul, inv_mul_cancel]
    simp only [rowAction_apply,map_one,vecMul_one]

/-- The image of the displacement on a canonical layer. -/
def movedBy (C : Subgroup Model) (n : ℕ) (x : Model) : Submodule (ZMod 2) V :=
  (layer C n).map (displacement x)

theorem movedBy_conj (C : Subgroup Model) (n : ℕ) (g x : Model)
    (hg : g ∈ normalizer (C : Set Model)) :
    (movedBy C n x).map (rowAction g).toLinearMap = movedBy C n (g⁻¹*x*g) := by
  unfold movedBy
  rw [← Submodule.map_comp]
  have he : (rowAction g).toLinearMap.comp (displacement x) =
      (displacement (g⁻¹*x*g)).comp (rowAction g).toLinearMap :=
    LinearMap.ext (rowAction_displacement g x)
  rw [he,Submodule.map_comp,layer_map C n g hg]

/-- Failure to fill the next layer is intrinsic to the entire normalizer. -/
theorem defect_conj_iff (C : Subgroup Model) (n : ℕ) (g x : Model)
    (hg : g ∈ normalizer (C : Set Model)) :
    movedBy C n (g⁻¹*x*g) = layer C (n+1) ↔ movedBy C n x = layer C (n+1) := by
  constructor
  · intro h
    apply Submodule.map_injective_of_injective (rowAction g).injective
    rw [movedBy_conj C n g x hg,layer_map C (n+1) g hg,h]
  · intro h
    rw [← movedBy_conj C n g x hg,h,layer_map C (n+1) g hg]



open Subgroup
open scoped IsMulCommutative

/-- The four fixed kernel elements followed by the four corrected source lifts. -/
def nativeGenerator (i : Fin 8) : Model := Fin.addCases (m := 4) (n := 4) (motive := fun _ => Model)
  (fun i => ((kernelVector 0 i).toMul : Model))
  (fun i => ((liftVector 0 i).toMul : Model)) i

theorem nativeGenerator_mem (i : Fin 8) : nativeGenerator i ∈ nativeEight 0 := by
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro j; simpa only [nativeGenerator, Fin.addCases_left] using (kernelVector 0 j).toMul.property
  · intro j; simpa only [nativeGenerator, Fin.addCases_right] using (liftVector 0 j).toMul.property

/-- The coordinate bijection proves generation by these eight actual elements. -/
theorem nativeGenerator_closure : closure (Set.range nativeGenerator) = nativeEight 0 := by
  apply le_antisymm
  · exact (closure_le _).mpr (Set.range_subset_iff.mpr nativeGenerator_mem)
  · intro x hx
    let H := closure (Set.range nativeGenerator)
    have hk (i : Fin 4) : ((kernelVector 0 i).toMul : Model) ∈ H :=
      subset_closure ⟨Fin.castAdd 4 i, by simp only [nativeGenerator, Fin.addCases_left]⟩
    have hl (i : Fin 4) : ((liftVector 0 i).toMul : Model) ∈ H :=
      subset_closure ⟨Fin.natAdd 4 i, by simp only [nativeGenerator, Fin.addCases_right]⟩
    have hsmul (v : Additive (nativeEight 0)) (hv : (v.toMul : Model) ∈ H) (a : ZMod 2) :
        ((a • v).toMul : Model) ∈ H := by
      fin_cases a
      · change (((0 : ZMod 2) • v).toMul : Model) ∈ H
        simpa only [zero_smul, toMul_zero, OneMemClass.coe_one] using H.one_mem
      · change (((1 : ZMod 2) • v).toMul : Model) ∈ H
        simpa only [one_smul] using hv
    have hsum (v : Fin 4 → Additive (nativeEight 0))
        (hv : ∀ i, ((v i).toMul : Model) ∈ H) :
        (((∑ i, v i).toMul) : Model) ∈ H := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      exact H.mul_mem (hv 0) (H.mul_mem (hv 1) (H.mul_mem (hv 2) (hv 3)))
    obtain ⟨⟨v,w⟩,he⟩ := eightCoordinates_surjective 0 (Additive.ofMul ⟨x,hx⟩)
    have hm := H.mul_mem (hsum _ (fun i => hsmul _ (hk i) (v i)))
      (hsum _ (fun i => hsmul _ (hl i) (w i)))
    change (((eightCoordinates 0 (v,w)).toMul) : Model) ∈ H at hm
    rwa [he] at hm

private theorem displacement_mul (a b : Model) (v : V) :
    displacement (a*b) v = displacement b (rowAction a v) + displacement a v := by
  simp only [displacement_apply,rowAction_mul]
  abel

private theorem displacement_inv (a : Model) (v : V) :
    displacement a⁻¹ v = -displacement a (rowAction a⁻¹ v) := by
  have he : rowAction a (rowAction a⁻¹ v) = v := by
    rw [← rowAction_mul,inv_mul_cancel]
    simp only [rowAction_apply,map_one,vecMul_one]
  rw [displacement_apply,displacement_apply,he]
  abel

theorem moved_eq_generators (C : Subgroup Model) (W : Submodule (ZMod 2) V)
    (hW : ∀ x ∈ C, ∀ v ∈ W, rowAction x v ∈ W)
    {ι : Type*} (g : ι → Model) (hg : closure (Set.range g) = C) :
    moved W C = Submodule.span (ZMod 2)
      {v | ∃ i, ∃ w ∈ W, displacement (g i) w = v} := by
  let S := Submodule.span (ZMod 2) {v | ∃ i, ∃ w ∈ W, displacement (g i) w = v}
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,hv,rfl⟩
    rw [← hg] at hx
    have hstep : ∀ v ∈ W, displacement x v ∈ S := by
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        intro v hv
        exact Submodule.subset_span ⟨i,v,hv,rfl⟩
      | one =>
        intro v hv
        simpa only [displacement_apply,rowAction_apply,map_one,vecMul_one,sub_self] using S.zero_mem
      | mul x y hx hy ihx ihy =>
        intro v hv
        rw [displacement_mul]
        exact S.add_mem (ihy _ (hW x (hg ▸ hx) v hv)) (ihx v hv)
      | inv x hx ihx =>
        intro v hv
        rw [displacement_inv]
        exact S.neg_mem (ihx _ (hW x⁻¹ (C.inv_mem (hg ▸ hx)) v hv))
    exact hstep v hv
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,v,hv,rfl⟩
    apply Submodule.subset_span
    exact ⟨g i,hg ▸ subset_closure (Set.mem_range_self i),v,hv,rfl⟩

/-- The eight literal generators suffice to compute every canonical layer. -/
theorem native_layer_succ (n : ℕ) :
    layer (nativeEight 0) (n+1) = Submodule.span (ZMod 2)
      {v | ∃ i : Fin 8, ∃ w ∈ layer (nativeEight 0) n,
        displacement (nativeGenerator i) w = v} :=
  moved_eq_generators _ _
    (fun x hx v hv => layer_stable _ n x ((nativeEight 0).le_normalizer hx) v hv)
    nativeGenerator nativeGenerator_closure



/-- The elements whose displacement fails to fill the fourth canonical layer.
This is a set until its equality with the native isotropic subgroup is certified. -/
def nativeDefectSet : Set Model :=
  {x | x ∈ nativeEight 0 ∧ movedBy (nativeEight 0) 3 x ≠ layer (nativeEight 0) 4}

/-- Unconditional invariance under the entire ambient normalizer of the eight. -/
theorem nativeDefectSet_normalizer :
    normalizer (nativeEight 0 : Set Model) ≤ normalizer nativeDefectSet := by
  intro g hg
  apply mem_set_normalizer_iff''.mpr
  intro x
  change (x ∈ nativeEight 0 ∧ movedBy (nativeEight 0) 3 x ≠ layer (nativeEight 0) 4) ↔
    (g⁻¹*x*g ∈ nativeEight 0 ∧
      movedBy (nativeEight 0) 3 (g⁻¹*x*g) ≠ layer (nativeEight 0) 4)
  exact and_congr (mem_normalizer_iff''.mp hg x)
    (not_congr (defect_conj_iff (nativeEight 0) 3 g x hg)).symm

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
