module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.RootWords
import Mathlib.Tactic

/-!
# Parity of any symmetry factorization of an actual Spin point

Each anisotropic symmetry is implemented by its invertible Clifford vector.
The product has the parity of the length of the symmetry word. The split
Clifford centralizer theorem forces an implementer of a Spin action to be even,
so every such word has even length, regardless of its coefficient field.

The unit construction follows `SplitOrthogonalLipschitzGeneration`; the parity
argument refines `AlgebraicGroups.EvenSpinDerivedRange`. Sources: GLS3, §§1.10
and 2.7 (the characteristic-two Dickson component).
-/

@[expose] public section
noncomputable section
universe u
namespace Theory.AlgebraicGroup.RationalOrthogonal
open _root_.CliffordAlgebra
variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}

private noncomputable def cliffordVectorUnit
    (a : {v : V // Q v ≠ 0}) : (CliffordAlgebra Q)ˣ := by
  letI : Invertible (Q a.1) := invertibleOfNonzero a.2
  letI : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  exact unitOfInvertible (CliffordAlgebra.ι Q a.1)

private lemma cliffordVectorUnit_coe
    (a : {v : V // Q v ≠ 0}) :
    (cliffordVectorUnit a : CliffordAlgebra Q) = CliffordAlgebra.ι Q a.1 := by
  simp [cliffordVectorUnit]

private lemma cliffordVectorUnit_mem_lipschitzGroup
    (a : {v : V // Q v ≠ 0}) :
    cliffordVectorUnit a ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  exact ⟨a.1, cliffordVectorUnit_coe a⟩

private lemma cliffordVectorUnit_conjugation
    (a : {v : V // Q v ≠ 0}) (x : V) :
    (cliffordVectorUnit a : CliffordAlgebra Q) * CliffordAlgebra.ι Q x *
        (↑((cliffordVectorUnit a)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (conjugationSymmetry Q a.1 a.2 x) := by
  let _ : Invertible (Q a.1) := invertibleOfNonzero a.2
  let _ : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  rw [cliffordVectorUnit_coe]
  change CliffordAlgebra.ι Q a.1 * CliffordAlgebra.ι Q x *
      ⅟(CliffordAlgebra.ι Q a.1) = _
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  simp only [conjugationSymmetry_apply, invOf_eq_inv]

private lemma cliffordVectorUnits_prod_mem_lipschitzGroup
    (as : List {v : V // Q v ≠ 0}) :
    (as.map cliffordVectorUnit).prod ∈ lipschitzGroup Q := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simpa using (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup a) ih

private lemma cliffordVectorUnits_prod_conjugation
    (as : List {v : V // Q v ≠ 0}) (x : V) :
    CliffordAlgebra.ι Q
        (as.foldr (fun a w => conjugationSymmetry Q a.1 a.2 w) x) =
      ((as.map cliffordVectorUnit).prod : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q x *
        (↑((as.map cliffordVectorUnit).prod⁻¹) : CliffordAlgebra Q) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [← cliffordVectorUnit_conjugation, ih]
      simp only [Units.val_mul, mul_inv_rev]
      simp only [mul_assoc]


private theorem cliffordVectorUnits_prod_grade (as : List (AnisotropicVector Q)) :
    ((as.map cliffordVectorUnit).prod : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := by
  induction as with
  | nil => simpa using (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul,
        cliffordVectorUnit_coe, List.length_cons, Nat.cast_add, Nat.cast_one]
      simpa [add_comm] using SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mem_evenOdd_one Q a.1) ih

/-- An even Clifford implementer forces every symmetry factorization to be even. -/
theorem even_length_of_even_implementer [IsAlgClosed k] [FiniteDimensional k V]
    (s : SplitQuadraticForm Q) (hs : 0 < s.rank)
    (a : (CliffordAlgebra Q)ˣ) (ha : (a : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (as : List (AnisotropicVector Q))
    (hconj : ∀ v : V, CliffordAlgebra.ι Q ((symmetryProductPoint as).1 v) =
      (a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹)) :
    Even as.length := by
  let : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  let b : (CliffordAlgebra Q)ˣ := (as.map cliffordVectorUnit).prod
  have hbLip : b ∈ lipschitzGroup Q := cliffordVectorUnits_prod_mem_lipschitzGroup as
  have hsame (v : V) :
      (a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹) =
        (b : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(b⁻¹) := by
    rw [← hconj, symmetryProductPoint_apply]
    exact cliffordVectorUnits_prod_conjugation as v
  have hquot : (↑(a * b⁻¹) : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q :=
    CliffordAlgebra.mul_inv_mem_even_of_mem_even_of_lipschitzGroup s hs ha hbLip hsame
  have hbGrade : (b : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := cliffordVectorUnits_prod_grade as
  have haGrade : (a : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (as.length : ZMod 2) := by
    simpa [mul_assoc] using SetLike.mul_mem_graded hquot hbGrade
  by_contra hne
  have hcast : (as.length : ZMod 2) = 1 := (Nat.not_even_iff_odd.mp hne).natCast_zmod_two
  rw [hcast] at haGrade
  have hzero : (a : CliffordAlgebra Q) ∈ (⊥ : Submodule k (CliffordAlgebra Q)) :=
    (CliffordAlgebra.evenOdd_isCompl Q).disjoint.le_bot ⟨ha, haGrade⟩
  exact Units.ne_zero a (by simpa only [Submodule.mem_bot] using hzero)

end Theory.AlgebraicGroup.RationalOrthogonal

namespace Triality.BinaryDegree.CarrierTransport
open Theory.AlgebraicGroup Triality.SimplyConnected
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The actual Spin carrier, rather than matrix rationality, supplies even parity. -/
theorem symmetryFactorization_even (g : Points k)
    (as : List (AnisotropicVector (quadraticForm k)))
    (hfac : symmetryProductPoint as = naturalAction k g) : Even as.length := by
  apply RationalOrthogonal.even_length_of_even_implementer
    (standardHyperbolicSplit 4) (by simp) (spinGroup.toUnits (pointEquiv k g))
    (spinGroup.mem_even (pointEquiv k g).property) as
  intro v
  rw [hfac]
  exact naturalAction_clifford k g v

end Triality.BinaryDegree.CarrierTransport
