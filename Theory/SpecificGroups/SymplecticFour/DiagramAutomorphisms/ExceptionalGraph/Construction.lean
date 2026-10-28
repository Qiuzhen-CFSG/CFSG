module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Theory.Representation.FirstCohomologySymplecticFour.Generation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
/-!
# The exceptional graph automorphism on symplectic matrices

In characteristic two, the second exterior power has a four-dimensional
symplectic quotient. Its matrix in the ordered coordinates
`e₀∧e₁, e₀∧f₁, f₀∧f₁, e₁∧f₀` consists of the minors defined below.
The symplectic row and column equations cancel the two omitted coordinates;
two polynomial identities prove multiplicativity and preservation of the form.

On the eight standard root families this exchanges long and short roots,
squaring precisely the short-root parameters. Root generation then proves
that the square is entrywise Frobenius. Over a finite field this supplies
bijectivity, giving an automorphism of the actual matrix group.

Source: GLS3, Theorem 2.5.1, exceptional B₂ formula, and Theorem 2.5.12(e),
`refs/KGroup/GLS3/chapter2.tex`; the cyclic outer group used in
Aschbacher--Smith, Proposition 1.3.4, printed p.511 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {F : Type*} [Field F] [CharP F 2]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "a" => (Sum.inl (0 : Fin 2) : I)
local notation "b" => (Sum.inl (1 : Fin 2) : I)
local notation "c" => (Sum.inr (0 : Fin 2) : I)
local notation "d" => (Sum.inr (1 : Fin 2) : I)


def first : I → I := Sum.elim ![a,a] ![c,b]
def second : I → I := Sum.elim ![b,d] ![d,c]
def minor (M : Matrix I I F) (i j k l : I) : F := M i k * M j l + M i l * M j k

def graphMatrix (M : Matrix I I F) : Matrix I I F :=
  fun i j => minor M (first i) (second i) (first j) (second j)

private def pairing (u v : I → F) : F := u a*v c+u b*v d+u c*v a+u d*v b
private lemma pairing_rows (g : Sp F) (i j : I) : pairing (g.val i) (g.val j) = Matrix.J (Fin 2) F i j := by
  have h := congrArg (fun M : Matrix I I F => M i j) g.property
  simpa [pairing, Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.one_apply, Matrix.transpose_apply, CharTwo.neg_eq, add_assoc, add_comm, add_left_comm] using h
private lemma pairing_cols (g : Sp F) (i j : I) :
    pairing (fun k => g.val k i) (fun k => g.val k j) = Matrix.J (Fin 2) F i j :=
  pairing_rows ⟨g.val.transpose, SymplecticGroup.transpose_mem g.property⟩ i j
private lemma pairing_first_second (g : Sp F) (i : I) :
    pairing (g.val (first i)) (g.val (second i)) = 0 := by
  rw [pairing_rows]
  rcases i with i|i <;> fin_cases i <;> simp [first, second, Matrix.J, Matrix.fromBlocks]

set_option maxHeartbeats 800000 in
private lemma minor_mul (g h : Sp F) (i j k l : I)
    (hg : pairing (g.val i) (g.val j) = 0)
    (hh : pairing (fun r => h.val r k) (fun r => h.val r l) = 0) :
    minor (g.val*h.val) i j k l =
      minor g.val i j a b * minor h.val a b k l +
      minor g.val i j a d * minor h.val a d k l +
      minor g.val i j c d * minor h.val c d k l +
      minor g.val i j b c * minor h.val b c k l := by
  simp only [minor, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  dsimp [pairing] at hg hh
  linear_combination (norm := skip)
    (g.val i a * g.val j c + g.val i c * g.val j a) * hh +
    (h.val b k * h.val d l + h.val d k * h.val b l) * hg
  ring_nf
  simp [CharTwo.two_eq_zero]

lemma graphMatrix_mul (g h : Sp F) : graphMatrix (g.val * h.val) = graphMatrix g.val * graphMatrix h.val := by
  ext i j
  have hc : pairing (fun k => h.val k (first j)) (fun k => h.val k (second j)) = 0 := by
    rw [pairing_cols]
    rcases j with j|j <;> fin_cases j <;> simp [first, second, Matrix.J, Matrix.fromBlocks]
  exact (minor_mul g h _ _ _ _ (pairing_first_second g i) hc).trans (by
    simp [graphMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, first, second, add_assoc])

-- bilinear exterior-square identity
set_option maxHeartbeats 800000 in
private lemma minor_pairing (M : Matrix I I F) (i j k l : I)
    (hij : pairing (M i) (M j) = 0) (hkl : pairing (M k) (M l) = 0) :
    minor M i j a b * minor M k l c d +
      minor M i j a d * minor M k l b c +
      minor M i j c d * minor M k l a b +
      minor M i j b c * minor M k l a d =
      pairing (M i) (M k) * pairing (M j) (M l) +
      pairing (M i) (M l) * pairing (M j) (M k) := by
  dsimp [minor, pairing] at *
  linear_combination (norm := skip)
    (M i a * M j c + M i c * M j a) * hkl +
    (M k b * M l d + M k d * M l b) * hij
  ring_nf
  simp [CharTwo.two_eq_zero]

lemma graphMatrix_mem (g : Sp F) : graphMatrix g.val ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  have hp := minor_pairing g.val (first i) (second i) (first j) (second j)
    (pairing_first_second g i) (pairing_first_second g j)
  simp only [pairing_rows] at hp
  have hm : (graphMatrix g.val * Matrix.J (Fin 2) F * (graphMatrix g.val).transpose) i j =
      pairing (graphMatrix g.val i) (graphMatrix g.val j) := by
    simp [pairing, Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.one_apply, Matrix.transpose_apply, CharTwo.neg_eq, add_assoc, add_comm, add_left_comm]
  rw [hm]
  change (minor _ _ _ a b * minor _ _ _ c d + minor _ _ _ a d * minor _ _ _ b c +
    minor _ _ _ c d * minor _ _ _ a b + minor _ _ _ b c * minor _ _ _ a d) = _
  rw [hp]
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [first, second, Matrix.J, Matrix.fromBlocks, CharTwo.neg_eq]

omit [CharP F 2] in
lemma graphMatrix_one : graphMatrix (1 : Matrix I I F) = 1 := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [graphMatrix, minor, first, second, Matrix.one_apply]

def graphEnd : Sp F →* Sp F where
  toFun g := ⟨graphMatrix g.val, graphMatrix_mem g⟩
  map_one' := Subtype.ext graphMatrix_one
  map_mul' g h := Subtype.ext (graphMatrix_mul g h)

open Representation.OneCohomology.SymplecticFour

def rootPermutation : Fin 8 → Fin 8 := ![4,5,6,7,0,1,2,3]
def rootParameter (r : Fin 8) (t : F) : F := if r.val < 4 then t else t^2

set_option maxHeartbeats 800000 in
lemma graphEnd_root (r : Fin 8) (t : F) :
    graphEnd (rootElement r t) = rootElement (rootPermutation r) (rootParameter r t) := by
  apply Subtype.ext
  ext i j
  fin_cases r <;> rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;>
    simp [graphEnd, graphMatrix, minor, first, second, rootElement, rootMatrix,
      rootPermutation, rootParameter, Matrix.fromBlocks, Matrix.single,
      CharTwo.neg_eq, pow_two]

variable [Finite F]

omit [CharP F 2] [Finite F] in
lemma fieldAutomorphism_root (σ : F ≃+* F) (r : Fin 8) (t : F) :
    fieldAutomorphism σ (rootElement r t) = rootElement r (σ t) := by
  apply Subtype.ext
  ext i j
  change σ ((rootMatrix r t) i j) = rootMatrix r (σ t) i j
  fin_cases r <;> rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.single]

lemma graphEnd_square : graphEnd.comp graphEnd =
    (fieldAutomorphism (frobeniusEquiv F 2)).toMonoidHom := by
  apply MonoidHom.eq_of_eqOn_dense rootElements_generate
  rintro _ ⟨⟨r,t⟩, rfl⟩
  change graphEnd (graphEnd (rootElement r t)) = fieldAutomorphism (frobeniusEquiv F 2) (rootElement r t)
  rw [graphEnd_root, graphEnd_root, fieldAutomorphism_root]
  fin_cases r <;> simp [rootPermutation, rootParameter, frobenius_def]

lemma graphEnd_bijective : Function.Bijective (graphEnd (F := F)) := by
  have hs : Function.Bijective ((graphEnd (F := F)).comp graphEnd) := by
    rw [graphEnd_square]
    exact (fieldAutomorphism (frobeniusEquiv F 2)).bijective
  constructor
  · intro x y h
    exact hs.1 (congrArg graphEnd h)
  · intro y
    obtain ⟨x, hx⟩ := hs.2 y
    exact ⟨graphEnd x, hx⟩

noncomputable def graphAut : MulAut (Sp F) := MulEquiv.ofBijective graphEnd graphEnd_bijective

@[simp] lemma graphAut_apply (g : Sp F) : graphAut g = graphEnd g := rfl

lemma graphAut_square : graphAut (F := F) ^ 2 = fieldAutomorphism (frobeniusEquiv F 2) := by
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun graphEnd_square g
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
