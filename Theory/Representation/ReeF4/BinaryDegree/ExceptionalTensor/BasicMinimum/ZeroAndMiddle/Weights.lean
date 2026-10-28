module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
public import Theory.AlgebraicGroup.Bor1.CommonEigenspaces

/-!
# Distinct coroot weights in the middle-node F4 modules

Simple normalizer words send a coroot weight `c` to
`c[j] - c[i] * Cartan[i,j]`. A fixed list of 26 words gives distinct weights
from each highest weight `(0,0,1,b)`, for `b = 0,1`; the finite integer
calculation is checked by the kernel. Nonzero Weyl translates are linearly
independent because their simultaneous coroot characters are distinct over
an algebraically closed field. No semisimplicity or highest-weight uniqueness
hypothesis is used in this counting argument.

Source: GLS3, §1.14 and Definition 2.8.1(b). The words were selected from the
parent's exploratory `Scratch/ReeF4BasicMinimum/orbits.py`; their certification
and their transport to the actual algebraic action are both proved here.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle

abbrev CorootWeight := Fin 4 → ℤ

@[expose] def reflectWeight (i : Fin 4) (c : CorootWeight) : CorootWeight :=
  fun j => c j - c i * typeF4CartanMatrix i j

@[expose] def reflectWord (word : List (Fin 4)) (c : CorootWeight) : CorootWeight :=
  word.foldl (fun c i => reflectWeight i c) c

private def middleWords : Fin 26 → List (Fin 4) :=
  ![[],
    [2],
    [2, 1],
    [2, 3],
    [2, 1, 0],
    [2, 1, 2],
    [2, 1, 3],
    [2, 1, 0, 2],
    [2, 1, 0, 3],
    [2, 1, 2, 3],
    [2, 1, 3, 2],
    [2, 1, 0, 2, 1],
    [2, 1, 0, 2, 3],
    [2, 1, 0, 3, 2],
    [2, 1, 2, 3, 2],
    [2, 1, 3, 2, 1],
    [2, 1, 0, 2, 1, 2],
    [2, 1, 0, 2, 1, 3],
    [2, 1, 0, 2, 3, 2],
    [2, 1, 0, 3, 2, 1],
    [2, 1, 2, 3, 2, 1],
    [2, 1, 3, 2, 1, 0],
    [2, 1, 0, 2, 1, 2, 3],
    [2, 1, 0, 2, 1, 3, 2],
    [2, 1, 0, 2, 3, 2, 1],
    [2, 1, 0, 3, 2, 1, 0]]

private theorem middleWords_distinct (b : Fin 2) :
    Function.Injective (fun n => reflectWord (middleWords n) ![0, 0, 1, (b.val : ℤ)]) := by
  fin_cases b <;> decide

variable {F : Type*} [Field F] [IsAlgClosed F]

@[expose] def IsCorootWeightVector (B : AlgebraicFactor F) (c : CorootWeight) (v : B.Space) : Prop :=
  v ≠ 0 ∧ ∀ (i : Fin 4) (t : Fˣ),
    (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ c i • v

theorem corootCharacters_injective :
    Function.Injective (fun c : CorootWeight => fun p : Fin 4 × Fˣ => (p.2 : F) ^ c p.1) := by
  intro c d h
  funext i
  by_contra hi
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one (k := F) (sub_ne_zero.mpr hi)
  apply ht
  rw [zpow_sub, mul_inv_eq_one]
  apply Units.ext
  simpa using congrFun h (i, t)

theorem corootWeightVectors_linearIndependent {ι : Type*}
    (B : AlgebraicFactor F) (c : ι → CorootWeight) (hc : Function.Injective c)
    (v : ι → B.Space) (hv : ∀ i, IsCorootWeightVector B (c i) (v i)) :
    LinearIndependent F v := by
  let f : (Fin 4 × Fˣ) → Module.End F B.Space := fun p =>
    (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex p.1) p.2) :
      Module.End F B.Space)
  have hχ := corootCharacters_injective (F := F) |>.comp hc
  have hL : iSupIndep (fun i : ι => ⨅ p : Fin 4 × Fˣ,
      (f p).eigenspace ((p.2 : F) ^ c i p.1)) :=
    (Bor1.iSupIndep_commonEigenspaces f).comp hχ
  apply hL.linearIndependent _
  · intro i
    rw [Submodule.mem_iInf]
    intro p
    exact Module.End.mem_eigenspace_iff.mpr ((hv i).2 p.1 p.2)
  · exact fun i => (hv i).1

theorem IsCorootWeightVector.reflect {B : AlgebraicFactor F} {c : CorootWeight}
    {v : B.Space} (hv : IsCorootWeightVector B c v) (i : Fin 4) :
    IsCorootWeightVector B (reflectWeight i c)
      ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) v) := by
  constructor
  · intro hz
    apply hv.1
    apply ((LinearMap.GeneralLinearGroup.generalLinearEquiv F B.Space)
      (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1))).injective
    simpa using hz
  · intro j t
    change ((B.action.action _ * B.action.action _ : LinearMap.GeneralLinearGroup F B.Space) :
      Module.End F B.Space) v = _
    rw [← map_mul, coroot_n_commute, map_mul, map_mul]
    change (B.action.action _ : Module.End F B.Space)
      ((B.action.action _ : Module.End F B.Space)
        ((B.action.action _ : Module.End F B.Space) v)) = _
    rw [hv.2, map_smul, hv.2, map_smul]
    rw [map_smul, smul_smul]
    congr 1
    simp only [reflectWeight, Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_add₀ t.ne_zero]
    congr 1
    ring

theorem exists_corootWeightVector_word (B : AlgebraicFactor F) (word : List (Fin 4))
    {c : CorootWeight} (hv : ∃ v, IsCorootWeightVector B c v) :
    ∃ w, IsCorootWeightVector B (reflectWord word c) w := by
  induction word generalizing c with
  | nil => exact hv
  | cons i word ih =>
    obtain ⟨v, hv⟩ := hv
    exact ih ⟨_, hv.reflect i⟩

theorem middle_finrank_ge (B : AlgebraicFactor F) (b : Fin 2)
    (h : B.HasBasicHighestWeight (1, b)) : 26 ≤ Module.finrank F B.Space := by
  classical
  obtain ⟨v, hv⟩ := h
  have hstart : IsCorootWeightVector B ![0, 0, 1, (b.val : ℤ)] v := by
    refine ⟨hv.1, ?_⟩
    intro i t
    have hh := hv.2.2 i t
    fin_cases i <;> simpa [basicCoefficient] using hh
  have hwords (n : Fin 26) : ∃ w,
      IsCorootWeightVector B (reflectWord (middleWords n) ![0, 0, 1, (b.val : ℤ)]) w :=
    exists_corootWeightVector_word B _ ⟨v, hstart⟩
  choose w hw using hwords
  have hind := corootWeightVectors_linearIndependent B _ (middleWords_distinct b) w hw
  simpa only [Fintype.card_fin] using hind.fintype_card_le_finrank

end ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
