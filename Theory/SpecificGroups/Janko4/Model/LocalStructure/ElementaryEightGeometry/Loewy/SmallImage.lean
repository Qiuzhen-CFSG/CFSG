module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.SmallRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Sparse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The four-coordinate displacement image

The sparse preimages in `SmallRows` span all four coordinates precisely outside
the displayed binary code. On the code a checked nonzero annihilator separates
the image from a coordinate vector. Thus no rank computation is assumed.
The semantic row equations expose `Vector.ofFn` projections before the finite
checks, retaining the literal generator and coordinate conventions.

This supplies the finite image criterion in the native invariant-subspace proof
of Kleidman--Wilson (1988), Corollary 2.3.6, printed p.493.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Matrix GeneratorCertificates

abbrev Four := Fin 4 → ZMod 2

def smallDecode (m : ℕ) : Four := fun i => bit m i.val

def smallRows (m : Fin 256) : Vector ℕ 32 := Vector.ofFn (fun j =>
  xorList (List.ofFn (fun i : Fin 8 => if m.val.testBit i.val then (thirdActions.get i).get j else 0)))

theorem smallRows_get (m : Fin 256) (j : Fin 32) :
    (smallRows m).get j =
      xorList (List.ofFn (fun i : Fin 8 =>
        if m.val.testBit i.val then (thirdActions.get i).get j else 0)) := by
  rw [smallRows, get_ofFn]

private theorem smallRows_get_fun (m : Fin 256) :
    (smallRows m).get = fun j =>
      xorList (List.ofFn (fun i : Fin 8 =>
        if m.val.testBit i.val then (thirdActions.get i).get j else 0)) := by
  funext j
  exact smallRows_get m j

def isotropicCode (m : Fin 256) : Prop :=
  bit m.val 0 + bit m.val 1 + bit m.val 2 + bit m.val 3 = 0 ∧
  bit m.val 4 = 0 ∧ bit m.val 5 = 0 ∧ bit m.val 6 = 0

instance (m : Fin 256) : Decidable (isotropicCode m) := by unfold isotropicCode; infer_instance

def smallSpan (m : Fin 256) : Submodule (ZMod 2) Four :=
  Submodule.span (ZMod 2) (Set.range (fun j : Fin 32 => smallDecode ((smallRows m).get j)))

theorem smallDecode_xor (m n : ℕ) : smallDecode (m ^^^ n) = smallDecode m + smallDecode n := by
  funext j
  exact bit_xor m n j.val

theorem smallDecode_xorList (ms : List ℕ) :
    smallDecode (xorList ms) = (ms.map smallDecode).sum := by
  induction ms with
  | nil =>
    funext j
    simp [smallDecode, bit, xorList]
  | cons m ms ih =>
    simpa only [xorList, smallDecode_xor, List.map_cons, List.sum_cons] using
      congrArg (smallDecode m + ·) ih

/-- The exact coefficient combination used by the third-layer displacement. -/
theorem smallDecode_smallRows (m : Fin 256) (j : Fin 32) :
    smallDecode ((smallRows m).get j) =
      ∑ i : Fin 8, bit m.val i.val • smallDecode ((thirdActions.get i).get j) := by
  funext k
  simp only [smallRows_get, smallDecode, bit_xorList, List.map_ofFn, List.sum_ofFn,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit]
  cases hm : m.val.testBit i.val <;> simp [hm]

theorem smallDecode_basis (i : Fin 4) : smallDecode (2^i.val) = Pi.single i 1 := by
  funext j
  simp [smallDecode,bit,Nat.testBit_two_pow,Pi.single_apply,Fin.ext_iff,eq_comm]

theorem smallDecode_sparse_mem (m : Fin 256) (indices : List (Fin 32)) :
    smallDecode (sparseCombine (smallRows m) indices) ∈ smallSpan m := by
  induction indices with
  | nil =>
    change smallDecode 0 ∈ smallSpan m
    have he : smallDecode 0 = 0 := by funext j; simp [smallDecode,bit]
    rw [he]; exact Submodule.zero_mem _
  | cons i indices ih =>
    change smallDecode ((smallRows m).get i ^^^ sparseCombine (smallRows m) indices) ∈ smallSpan m
    rw [smallDecode_xor]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self i)) ih

private theorem full_preimages_checked : ∀ a b : Fin 16, ∀ j : Fin 4,
    isotropicCode (finProdFinEquiv (a,b)) ∨
      sparseCombine (smallRows (finProdFinEquiv (a,b)))
        ((fullPreimages.get (finProdFinEquiv (a,b))).get j) = 2^j.val := by
  simp only [sparseCombine, smallRows_get_fun]
  decide +kernel

theorem small_full_preimages (m : Fin 256) (hm : ¬ isotropicCode m) (j : Fin 4) :
    sparseCombine (smallRows m) ((fullPreimages.get m).get j) = 2^j.val := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin 16 × Fin 16 ≃ Fin 256).surjective m
  rcases full_preimages_checked a b j with h | h
  · exact (hm h).elim
  · exact h

private theorem annihilator_checked : ∀ a b : Fin 16,
    ¬ isotropicCode (finProdFinEquiv (a,b)) ∨
      (∀ j : Fin 32,
        dotProduct (smallDecode (smallAnnihilator.get (finProdFinEquiv (a,b))))
          (smallDecode ((smallRows (finProdFinEquiv (a,b))).get j)) = 0) ∧
      smallDecode (smallAnnihilator.get (finProdFinEquiv (a,b)))
        (missingCoordinate.get (finProdFinEquiv (a,b))) = 1 := by
  simp only [smallRows_get]
  decide +kernel

theorem small_annihilator (m : Fin 256) (hm : isotropicCode m) :
    (∀ j : Fin 32, dotProduct (smallDecode (smallAnnihilator.get m))
      (smallDecode ((smallRows m).get j)) = 0) ∧
    smallDecode (smallAnnihilator.get m) (missingCoordinate.get m) = 1 := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin 16 × Fin 16 ≃ Fin 256).surjective m
  rcases annihilator_checked a b with h | h
  · exact (h hm).elim
  · exact h

/-- The four-coordinate small displacement image fills all coordinates exactly
off the displayed isotropic code. The finite witnesses are kernel-checked. -/
theorem smallSpan_eq_top_iff (m : Fin 256) : smallSpan m = ⊤ ↔ ¬ isotropicCode m := by
  constructor
  · intro h hm
    obtain ⟨ha,hne⟩ := small_annihilator m hm
    let f : Four →ₗ[ZMod 2] ZMod 2 :=
      dotProductBilin (ZMod 2) (ZMod 2) (smallDecode (smallAnnihilator.get m))
    have hz : smallSpan m ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change dotProduct (smallDecode (smallAnnihilator.get m))
        (smallDecode ((smallRows m).get j)) = 0
      exact ha j
    have hb : Pi.single (missingCoordinate.get m) 1 ∈ smallSpan m := by rw [h]; trivial
    have he := hz hb
    change dotProduct (smallDecode (smallAnnihilator.get m)) (Pi.single (missingCoordinate.get m) 1) = 0 at he
    rw [dotProduct_single_one,hne] at he
    exact one_ne_zero he
  · intro hm
    apply top_unique
    rw [← (Pi.basisFun (ZMod 2) (Fin 4)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [Pi.basisFun_apply,← smallDecode_basis,← small_full_preimages m hm i]
    exact smallDecode_sparse_mem m _

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
