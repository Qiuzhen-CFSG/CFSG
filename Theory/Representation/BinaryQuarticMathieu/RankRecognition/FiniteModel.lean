module

public import Theory.Representation.BinaryQuarticMathieu.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Nat.Log

/-!
# Finite coordinates for the genuine quartic contraction rank

The binary words below enumerate the actual ten-dimensional space bijectively.
A functional is zero exactly when it vanishes on the standard basis. Thus the
kernel of a contraction is an explicitly testable set of 1024 words, and
rank-nullity identifies the intrinsic rank with ten minus the base-two logarithm
of that set's cardinality. The matrix bridge retains the entries of the actual
alternating form; it does not replace the form by a table of asserted ranks.

This supplies the semantic boundary for checking the untrusted representative
histograms in `../source/generate_orbits.py`. No orbit or nonzero histogram is
assumed or certified in this module.
-/

@[expose] public section

namespace BinaryQuarticMathieu.RankRecognition
abbrev Word := Fin 1024

def decode (n : Word) : U := vector n.val

theorem decode_injective : Function.Injective decode := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · have hh := congrFun hab ⟨i, hi⟩
    change (if a.val.testBit i then (1 : F) else 0) =
      (if b.val.testBit i then (1 : F) else 0) at hh
    cases ha : a.val.testBit i <;> cases hb : b.val.testBit i <;> simp_all
  · have hpow : 1024 ≤ 2 ^ i := by
      calc
        1024 = 2 ^ 10 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hpow)]

theorem card_U : Nat.card U = 1024 := by
  rw [Nat.card_eq_fintype_card]
  simp [U, F]

theorem decode_bijective : Function.Bijective decode := by
  apply (Nat.bijective_iff_injective_and_card decode).mpr
  exact ⟨decode_injective, by simp⟩

noncomputable def decodeEquiv : Word ≃ U := Equiv.ofBijective decode decode_bijective

def basisVector (i : Fin 10) : U := Pi.single i 1

theorem contraction_mem_ker_iff (Q : Form) (v w x : U) :
    x ∈ (contraction Q v w).ker ↔ ∀ j, Q ![v,w,x,basisVector j] = 0 := by
  change contraction Q v w x = 0 ↔ _
  constructor
  · intro h j
    exact congrArg (fun f : Module.Dual F U => f (basisVector j)) h
  · intro h
    apply (Pi.basisFun F (Fin 10)).ext
    intro j
    simpa [Pi.basisFun_apply, basisVector] using h j

def kernelWords (Q : Form) (v w : U) : Finset Word :=
  Finset.univ.filter (fun n => ∀ j, Q ![v,w,decode n,basisVector j] = 0)

theorem kernelWords_card (Q : Form) (v w : U) :
    (kernelWords Q v w).card = Nat.card (contraction Q v w).ker := by
  have he : {n : Word // ∀ j, Q ![v,w,decode n,basisVector j] = 0} ≃
      (contraction Q v w).ker :=
    decodeEquiv.subtypeEquiv (fun n => (contraction_mem_ker_iff Q v w (decode n)).symm)
  rw [← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem contractionRank_eq_kernelWords (Q : Form) (v w : U) :
    contractionRank Q v w = 10 - Nat.log 2 (kernelWords Q v w).card := by
  have hc : (kernelWords Q v w).card = 2 ^ Module.finrank F (contraction Q v w).ker := by
    rw [kernelWords_card, Module.natCard_eq_pow_finrank (K := F)]
    simp [F]
  rw [hc, Nat.log_pow (by decide)]
  have hd := (contraction Q v w).finrank_range_add_finrank_ker
  have hu : Module.finrank F U = 10 := by simp [U]
  rw [hu] at hd
  exact Nat.eq_sub_of_add_eq hd

/-- Any checked rank computation on the packed words determines the genuine
histogram. The hypothesis concerns the actual contraction image dimension. -/
theorem rankDistribution_eq_word_count (Q : Form) (v : U) (rank : Word → Nat)
    (h : ∀ n : Word, contractionRank Q v (decode n) = rank n) (r : Nat) :
    rankDistribution Q v r = (Finset.univ.filter (fun n : Word => rank n = r)).card := by
  have e : {n : Word // rank n = r} ≃ {w : U // contractionRank Q v w = r} :=
    decodeEquiv.subtypeEquiv (fun n => by
      change rank n = r ↔ contractionRank Q v (decode n) = r
      rw [h n])
  unfold rankDistribution
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

def contractionMatrix (Q : Form) (v w : U) : Matrix (Fin 10) (Fin 10) F :=
  fun j i => Q ![v,w,basisVector i,basisVector j]

theorem contraction_basis_apply (Q : Form) (v w x : U) (j : Fin 10) :
    Q ![v,w,x,basisVector j] = ∑ i, x i * contractionMatrix Q v w j i := by
  have hx : ∑ i, x i • basisVector i = x := by
    simpa [Pi.basisFun_apply, basisVector] using (Pi.basisFun F (Fin 10)).sum_repr x
  change (contraction Q v w x) (basisVector j) = _
  rw [← hx, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  ext i
  rw [hx]
  rfl

def matrixKernelWords (M : Matrix (Fin 10) (Fin 10) F) : Finset Word :=
  Finset.univ.filter (fun n => ∀ j, ∑ i, decode n i * M j i = 0)

theorem kernelWords_eq_matrixKernelWords (Q : Form) (v w : U) :
    kernelWords Q v w = matrixKernelWords (contractionMatrix Q v w) := by
  ext n
  simp only [kernelWords, matrixKernelWords, Finset.mem_filter, Finset.mem_univ,
    true_and, contraction_basis_apply]

theorem contractionRank_eq_of_matrixKernel_card (Q : Form) (v w : U)
    (M : Matrix (Fin 10) (Fin 10) F) (r : Nat) (hr : r ≤ 10)
    (hM : M = contractionMatrix Q v w)
    (hc : (matrixKernelWords M).card = 2 ^ (10 - r)) :
    contractionRank Q v w = r := by
  rw [contractionRank_eq_kernelWords, kernelWords_eq_matrixKernelWords, ← hM, hc,
    Nat.log_pow (by decide), Nat.sub_sub_self hr]

theorem contraction_zero_left (Q : Form) (w : U) : contraction Q 0 w = 0 := by
  ext x y
  exact Q.map_coord_zero 0 rfl

theorem contractionRank_zero_left (Q : Form) (w : U) :
    contractionRank Q 0 w = 0 := by
  simp [contractionRank, contraction_zero_left]

def zeroDistribution (r : Nat) : Nat := if r = 0 then 1024 else 0

theorem rankDistribution_zero (Q : Form) : rankDistribution Q 0 = zeroDistribution := by
  funext r
  simp only [rankDistribution, contractionRank_zero_left, zeroDistribution]
  split_ifs with hr
  · subst r
    simp [Nat.card_eq_fintype_card, U, F]
  · have hne : (0 : Nat) ≠ r := Ne.symm hr
    simp [hne]

end BinaryQuarticMathieu.RankRecognition
