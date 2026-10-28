module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.FieldAction
public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry

/-!
# Rigidity of normalized Suzuki automorphisms

For `m ≥ 1`, an automorphism of the concrete Suzuki group which preserves
its root subgroup and split torus and fixes the Weyl element is a genuine
entrywise automorphism of the defining field.

Write `u(a,b)` for a root element and `w` for the Weyl element. The unit
Gauss relation `w u(0,1) w = u(1,1) w u(1,0)`, together with the square
formula, forces the image of `u(1,0)` to be itself. Torus conjugation then
identifies the images of `u(a,0)` and the torus by one field map. Root
multiplication proves additivity; torus conjugation proves multiplicativity.
The identity `u(b,0) u(1,0) = u(b+1,0) u(0,b)` determines the remaining
central coordinate. Equality extends from the root, torus and Weyl generators
to the entire matrix group.

This is the rigidity step toward GLS, Volume 4, Chapter 4, Lemma 3.1(a,b),
whose upstream automorphism statement is Volume 3, Theorem 2.5.12(b--f).
The coordinate formulas are Huppert--Blackburn III, XI.3.1 and XI.3.3, in
the transposed upper-triangular convention of `MatrixGroups.Suzuki`.
-/

namespace BenderSuzuki.MatrixGroups
open PFAppendixIII

private noncomputable def rigidityRoot (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m a b, Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩

private noncomputable def rigidityTorus (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m x, Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))⟩

@[simp] private theorem root_entry01 (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    (rigidityRoot m a b).val (0 : Fin 4) (1 : Fin 4) = a := rfl

@[simp] private theorem root_entry02 (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    (rigidityRoot m a b).val (0 : Fin 4) (2 : Fin 4) = b := rfl

private theorem root_injective (m : ℕ) {a b a' b' : BinaryGaloisField (2 * m + 1)}
    (h : rigidityRoot m a b = rigidityRoot m a' b') : a = a' ∧ b = b' := by
  exact ⟨congrArg (fun g : SuzukiMatrixGroup m => g.val (0 : Fin 4) (1 : Fin 4)) h,
    congrArg (fun g : SuzukiMatrixGroup m => g.val (0 : Fin 4) (2 : Fin 4)) h⟩

private theorem root_mem (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    rigidityRoot m a b ∈ SuzukiRootSubgroup m :=
  (mem_suzukiRootSubgroup_iff m _).mpr ⟨a, b, rfl⟩

private theorem torus_mem (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    rigidityTorus m x ∈ SuzukiSplitTorus m :=
  (mem_suzukiSplitTorus_iff m _).mpr ⟨x, rfl⟩

private theorem mem_root_iff (m : ℕ) (g : SuzukiMatrixGroup m) :
    g ∈ SuzukiRootSubgroup m ↔ ∃ a b, g = rigidityRoot m a b := by
  rw [mem_suzukiRootSubgroup_iff]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, Subtype.ext h⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩

private theorem mem_torus_iff (m : ℕ) (g : SuzukiMatrixGroup m) :
    g ∈ SuzukiSplitTorus m ↔ ∃ x, g = rigidityTorus m x := by
  rw [mem_suzukiSplitTorus_iff]
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, Subtype.ext h⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

@[simp] private theorem root_zero (m : ℕ) : rigidityRoot m 0 0 = 1 :=
  Subtype.ext (External.suzukiRootGL_zero_zero m)

private theorem root_mul (m : ℕ) (hm : 0 < m)
    (a b a' b' : BinaryGaloisField (2 * m + 1)) :
    rigidityRoot m a b * rigidityRoot m a' b' =
      rigidityRoot m (a + a') (b + b' + a * suzukiTits m a') := by
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.1 a b a' b'

private theorem torus_conj_root (m : ℕ)
    (x : (BinaryGaloisField (2 * m + 1))ˣ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    rigidityTorus m x * rigidityRoot m a b * (rigidityTorus m x)⁻¹ =
      rigidityRoot m (x * a) (x * suzukiTits m x * b) := by
  apply Subtype.ext
  exact External.suzukiTorusGL_conj_root m (suzukiTits m)
    (suzukiTits_sq m) (suzukiTits_apply m) a b x

private theorem field_root (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (a b : BinaryGaloisField (2 * m + 1)) :
    suzukiFieldAut m σ (rigidityRoot m a b) = rigidityRoot m (σ a) (σ b) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [rigidityRoot, SuzukiRootGL, SuzukiRootMatrix]

private theorem field_torus (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    suzukiFieldAut m σ (rigidityTorus m x) =
      rigidityTorus m (Units.map σ.toRingHom x) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [rigidityTorus, SuzukiTorusGL, SuzukiTorusMatrix]

private theorem field_weyl (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    suzukiFieldAut m σ (suzukiWeyl m) = suzukiWeyl m := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [suzukiWeyl, SuzukiWeylGL, SuzukiWeylMatrix]

private theorem aut_ext (m : ℕ) (α β : MulAut (SuzukiMatrixGroup m))
    (hu : ∀ a b, α (rigidityRoot m a b) = β (rigidityRoot m a b))
    (ht : ∀ x, α (rigidityTorus m x) = β (rigidityTorus m x))
    (hw : α (suzukiWeyl m) = β (suzukiWeyl m)) : α = β := by
  apply MulEquiv.ext
  rintro ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl
      · exact hu a b
      · exact ht x
      · exact hw
  | one => exact (map_one α).trans (map_one β).symm
  | mul g h hg hh ihg ihh =>
      change α (⟨g, hg⟩ * ⟨h, hh⟩) = β (⟨g, hg⟩ * ⟨h, hh⟩)
      rw [map_mul, map_mul, ihg, ihh]
  | inv g hg ih =>
      change α (⟨g, hg⟩⁻¹) = β (⟨g, hg⟩⁻¹)
      rw [map_inv, map_inv, ih]

private theorem root_weyl_unit_relation (m : ℕ) :
    suzukiWeyl m * rigidityRoot m 0 1 * suzukiWeyl m =
      rigidityRoot m 1 1 * suzukiWeyl m * rigidityRoot m 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rigidityRoot, suzukiWeyl, SuzukiRootGL, SuzukiRootMatrix,
      SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

private theorem root_sq (m : ℕ) (hm : 0 < m)
    (a b : BinaryGaloisField (2 * m + 1)) :
    rigidityRoot m a b * rigidityRoot m a b =
      rigidityRoot m 0 (a * suzukiTits m a) := by
  simp [root_mul m hm, CharTwo.add_self_eq_zero]

private theorem root_split (m : ℕ) (hm : 0 < m)
    (a b : BinaryGaloisField (2 * m + 1)) :
    rigidityRoot m a b = rigidityRoot m a 0 * rigidityRoot m 0 b := by
  simp [root_mul m hm]

private theorem aut_root_mem (m : ℕ) (β : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m)
    (a b : BinaryGaloisField (2 * m + 1)) :
    ∃ c d, β (rigidityRoot m a b) = rigidityRoot m c d := by
  apply (mem_root_iff m _).mp
  rw [← hU]
  exact Subgroup.mem_map_of_mem β.toMonoidHom (root_mem m a b)

private theorem aut_torus_mem (m : ℕ) (β : MulAut (SuzukiMatrixGroup m))
    (hT : (SuzukiSplitTorus m).map β.toMonoidHom = SuzukiSplitTorus m)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    ∃ y, β (rigidityTorus m x) = rigidityTorus m y := by
  apply (mem_torus_iff m _).mp
  rw [← hT]
  exact Subgroup.mem_map_of_mem β.toMonoidHom (torus_mem m x)

/-- The unit Gauss relation fixes the distinguished root element. -/
private theorem aut_root_one (m : ℕ) (hm : 0 < m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m)
    (hw : β (suzukiWeyl m) = suzukiWeyl m) :
    β (rigidityRoot m 1 0) = rigidityRoot m 1 0 := by
  obtain ⟨c, d, h⟩ := aut_root_mem m β hU 1 0
  have h01 : β (rigidityRoot m 0 1) = rigidityRoot m 0 (c * suzukiTits m c) := by
    have hs := congrArg β (root_sq m hm 1 0)
    rw [map_mul, h, root_sq m hm] at hs
    simpa using hs.symm
  have h11 : β (rigidityRoot m 1 1) =
      rigidityRoot m c (d + c * suzukiTits m c) := by
    rw [root_split m hm 1 1, map_mul, h, h01, root_mul m hm]
    simp
  have hr := congrArg β (root_weyl_unit_relation m)
  simp only [map_mul, hw, h01, h11, h] at hr
  have h30 := congrArg (fun g : SuzukiMatrixGroup m => g.val (3 : Fin 4) (0 : Fin 4)) hr
  have h31 := congrArg (fun g : SuzukiMatrixGroup m => g.val (3 : Fin 4) (1 : Fin 4)) hr
  have h32 := congrArg (fun g : SuzukiMatrixGroup m => g.val (3 : Fin 4) (2 : Fin 4)) hr
  simp [rigidityRoot, suzukiWeyl, SuzukiRootGL, SuzukiRootMatrix,
    SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] at h30 h31 h32
  have hc : c = 1 := by
    apply (suzukiTits m).injective
    rw [← h31]
    simpa [suzukiTits_apply] using h30
  simpa [hc, h32.symm] using h

/-- Squares detect the central coordinate without invoking a classification of U. -/
private theorem aut_root_central (m : ℕ) (hm : 0 < m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m)
    (b : BinaryGaloisField (2 * m + 1)) :
    ∃ d, β (rigidityRoot m 0 b) = rigidityRoot m 0 d := by
  obtain ⟨c, d, h⟩ := aut_root_mem m β hU 0 b
  have hs := congrArg β (root_sq m hm 0 b)
  rw [map_mul, h, root_sq m hm] at hs
  simp only [zero_mul, root_zero, map_one] at hs
  have hn := (root_injective m (hs.trans (root_zero m).symm)).2
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hn with hc | hc
    · exact hc
    · exact (map_eq_zero (suzukiTits m)).mp hc
  exact ⟨d, by simpa [hc] using h⟩

/-- On the first root coordinate a normalized automorphism is a field map. -/
private theorem aut_field_coordinate (m : ℕ) (hm : 0 < m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m)
    (hT : (SuzukiSplitTorus m).map β.toMonoidHom = SuzukiSplitTorus m)
    (hw : β (suzukiWeyl m) = suzukiWeyl m) :
    ∃ σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1),
      (∀ a, β (rigidityRoot m a 0) = rigidityRoot m (σ a) 0) ∧
      (∀ x, β (rigidityTorus m x) = rigidityTorus m (Units.map σ.toRingHom x)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let f : K → K := fun a => (β (rigidityRoot m a 0)).val (0 : Fin 4) (1 : Fin 4)
  have hone := aut_root_one m hm β hU hw
  have ht (x : Kˣ) : ∃ y : Kˣ,
      β (rigidityTorus m x) = rigidityTorus m y ∧
      β (rigidityRoot m x 0) = rigidityRoot m y 0 := by
    obtain ⟨y, hy⟩ := aut_torus_mem m β hT x
    refine ⟨y, hy, ?_⟩
    have h := congrArg β (torus_conj_root m x 1 0)
    rw [map_mul, map_mul, map_inv, hy, hone, torus_conj_root] at h
    simpa only [mul_one, mul_zero] using h.symm
  have hf0 : f 0 = 0 := by simp [f, root_zero]
  have hf1 : f 1 = 1 := by simp [f, hone]
  have hf (a : K) : β (rigidityRoot m a 0) = rigidityRoot m (f a) 0 := by
    by_cases ha : a = 0
    · simp [ha, hf0, root_zero]
    obtain ⟨y, _, hy⟩ := ht (Units.mk0 a ha)
    have he : f a = (y : K) := congrArg
      (fun g : SuzukiMatrixGroup m => g.val (0 : Fin 4) (1 : Fin 4)) hy
    rw [he]
    exact hy
  have hfirst (a b : K) :
      (β (rigidityRoot m a b)).val (0 : Fin 4) (1 : Fin 4) = f a := by
    obtain ⟨d, hd⟩ := aut_root_central m hm β hU b
    rw [root_split m hm a b, map_mul, hf, hd, root_mul m hm]
    simp
  have hadd (a b : K) : f (a + b) = f a + f b := by
    have h := congrArg β (root_mul m hm a 0 b 0)
    rw [map_mul, hf, hf, root_mul m hm] at h
    have he := congrArg
      (fun g : SuzukiMatrixGroup m => g.val (0 : Fin 4) (1 : Fin 4)) h
    simpa only [root_entry01, hfirst] using he.symm
  have hmul (a b : K) : f (a * b) = f a * f b := by
    by_cases ha : a = 0
    · simp [ha, hf0]
    obtain ⟨y, hy, hu⟩ := ht (Units.mk0 a ha)
    have he : (y : K) = f a := (root_injective m (hu.symm.trans (hf a))).1
    have h := congrArg β (torus_conj_root m (Units.mk0 a ha) b 0)
    rw [map_mul, map_mul, map_inv, hy, hf, torus_conj_root] at h
    simp only [mul_zero, Units.val_mk0, hf] at h
    exact (root_injective m h).1.symm.trans (by rw [he])
  let R : K →+* K :=
    { toFun := f
      map_one' := hf1
      map_mul' := hmul
      map_zero' := hf0
      map_add' := hadd }
  let F : K →ₐ[ZMod 2] K :=
    { R with
      commutes' := fun r => DFunLike.congr_fun
        (Subsingleton.elim (R.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)) r }
  let σ := AlgEquiv.ofBijective F
    ⟨F.toRingHom.injective, Finite.surjective_of_injective F.toRingHom.injective⟩
  refine ⟨σ, hf, ?_⟩
  intro x
  obtain ⟨y, hy, hu⟩ := ht x
  rw [hy]
  congr 1
  apply Units.ext
  exact (root_injective m (hu.symm.trans (hf x))).1

/-- Every automorphism preserving the standard root subgroup and split torus
and fixing the Weyl element is induced entrywise by a defining-field
automorphism over `ZMod 2`. -/
public theorem suzukiAut_eq_fieldAut_of_normalized (m : ℕ) (hm : 1 ≤ m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map β.toMonoidHom = SuzukiRootSubgroup m)
    (hT : (SuzukiSplitTorus m).map β.toMonoidHom = SuzukiSplitTorus m)
    (hw : β (suzukiWeyl m) = suzukiWeyl m) :
    ∃ σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1),
      β = suzukiFieldAut m σ := by
  obtain ⟨σ, hu, ht⟩ := aut_field_coordinate m hm β hU hT hw
  have hz (b : BinaryGaloisField (2 * m + 1)) :
      β (rigidityRoot m 0 b) = rigidityRoot m 0 (σ b) := by
    obtain ⟨d, hd⟩ := aut_root_central m hm β hU b
    have hp : rigidityRoot m b 0 * rigidityRoot m 1 0 =
        rigidityRoot m (b + 1) 0 * rigidityRoot m 0 b := by
      simp [root_mul m hm]
    have h := congrArg β hp
    rw [map_mul, map_mul, hu, hu, hu, hd] at h
    simp only [root_mul m hm, map_one, map_zero,
      zero_add, add_zero, mul_one, mul_zero] at h
    have he : σ b = d := (root_injective m h).2
    simpa [← he] using hd
  refine ⟨σ, aut_ext m β (suzukiFieldAut m σ) ?_ ?_ ?_⟩
  · intro a b
    rw [field_root, root_split m hm a b, map_mul, hu, hz, root_mul m hm]
    simp
  · intro x
    rw [ht, field_torus]
  · rw [hw, field_weyl]

end BenderSuzuki.MatrixGroups
