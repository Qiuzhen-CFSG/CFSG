module
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic

/-!
# Checked spectral polynomials for the binary endpoint induction

The five distinct irreducible polynomials have degrees 1, 4, 6, 14, 20. The
finite certificates consist of repeated-square reductions and Bezout
identities. Every identity is checked by the kernel; external computations
provide only witness data. A general finite-field Rabin criterion converts
these identities into irreducibility.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace BinaryEndpointInduction.SpectralPolynomials

/-- A finite-field Frobenius test, allowing any finite list of exponents
covering the possible proper irreducible factor degrees. -/
theorem irreducible_of_frobenius_tests
    {k : Type*} [Field k] [Finite k]
    (p : k[X]) (n : ℕ) (hn : 0<n) (hm : p.Monic) (hd : p.natDegree=n)
    (tests : Finset ℕ)
    (hfull : p ∣ X^(Nat.card k ^ n)-X)
    (hcop : ∀ m ∈ tests, IsCoprime p (X^(Nat.card k ^ m)-X))
    (hcover : ∀ d : ℕ, 0<d → d≤n/2 → d∣n → ∃ m ∈ tests, d∣m) :
    Irreducible p := by
  apply (hm.irreducible_iff_lt_natDegree_lt (by
    intro hp
    rw [hp,natDegree_one] at hd
    omega)).mpr
  intro q hq hdeg hqp
  obtain ⟨r,hr,hrq⟩ := exists_irreducible_of_natDegree_pos (Finset.mem_Ioc.mp hdeg).1
  have hrp : r ∣ p := hrq.trans hqp
  have hdn : r.natDegree ∣ n := hr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hrp.trans hfull)
  have hsmall : r.natDegree ≤ n/2 := by
    have hh := (natDegree_le_of_dvd hrq hq.ne_zero).trans (Finset.mem_Ioc.mp hdeg).2
    simpa only [hd] using hh
  obtain ⟨m,hmtest,hdm⟩ := hcover r.natDegree hr.natDegree_pos hsmall hdn
  have hrm : r ∣ X^(Nat.card k ^ m)-X := hr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hdm
  exact hr.not_isUnit ((hcop m hmtest).isUnit_of_dvd' hrp hrm)

/-- The exact degrees used by the two concrete endpoint inductions. -/
def degree : Fin 5 → ℕ := ![1,4,6,14,20]

/-- The common five spectral factors, with binary coefficients. -/
def polynomial : Fin 5 → (ZMod 2)[X] := ![
  X+1,
  X^4+X+1,
  X^6+X^4+X^3+X+1,
  X^14+X^7+X^5+X^3+1,
  X^20+X^10+X^9+X^7+X^6+X^5+X^4+X+1]

theorem natDegree (i : Fin 5) : (polynomial i).natDegree=degree i := by
  fin_cases i <;> dsimp [polynomial, degree] <;> compute_degree!

theorem monic (i : Fin 5) : (polynomial i).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [natDegree]
  fin_cases i <;> dsimp [polynomial, degree] <;> compute_degree!

private theorem reduction_divides {R : Type*} [CommRing R]
    (p : R[X]) (n : ℕ) (r : ℕ → R[X]) (q : ℕ → R[X])
    (hzero : r 0=X) (hstep : ∀ i<n, (r i)^2=p*q i+r (i+1)) :
    p ∣ X^(2^n)-r n := by
  let π := Ideal.Quotient.mk (Ideal.span ({p} : Set R[X]))
  have hp : π p=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton p))
  have hi : ∀ i≤n, π (r i)=(π X)^(2^i) := by
    intro i hin
    induction i with
    | zero => simp only [hzero,pow_zero,pow_one]
    | succ i ih =>
      have hh := congrArg π (hstep i (by omega))
      rw [map_pow,map_add,map_mul,hp,zero_mul,zero_add] at hh
      rw [←hh,ih (by omega),Nat.pow_succ,pow_mul]
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (X^(2^n)-r n)=0
  rw [map_sub,map_pow,hi n le_rfl,sub_self]

private theorem coprime_of_reduction
    (p r : (ZMod 2)[X]) (m : ℕ)
    (hred : p ∣ X^(2^m)-r) (hc : IsCoprime p (r-X)) :
    IsCoprime p (X^(2^m)-X) := by
  apply IsRelPrime.isCoprime
  intro d hdp hdf
  apply hc.isUnit_of_dvd' hdp
  have hh := dvd_sub hdf (hdp.trans hred)
  convert hh using 1; abel


private def ofExponents (degrees : List ℕ) : (ZMod 2)[X] :=
  (degrees.map fun d => (X : (ZMod 2)[X])^d).sum

private def remainders : Fin 5 → List ((ZMod 2)[X]) := ![
  [ofExponents [1],ofExponents [1]],
  [ofExponents [1],ofExponents [2],ofExponents [1,0],ofExponents [2,0],ofExponents [1]],
  [ofExponents [1],ofExponents [2],ofExponents [4],ofExponents [5,4,2,1,0],ofExponents [4,1,0],ofExponents [5,4,1],ofExponents [1]],
  [ofExponents [1],ofExponents [2],ofExponents [4],ofExponents [8],ofExponents [9,7,5,2],ofExponents [11,10,9,5,3,0],ofExponents [11,10,7,6,1,0],ofExponents [12,9,7,5,4,3,2,1],ofExponents [13,11,10,9,8,6,5,4,2,1,0],ofExponents [12,11,10,9,3,0],ofExponents [13,11,7,6,4,3,0],ofExponents [13,12,11,7],ofExponents [11,8,7,6,4,3,1,0],ofExponents [13,12,11,9,8,4,3,1],ofExponents [1]],
  [ofExponents [1],ofExponents [2],ofExponents [4],ofExponents [8],ofExponents [16],ofExponents [19,18,17,16,13,10,9,5,3,1],ofExponents [19,18,16,14,12,11,8,7,2,0],ofExponents [17,16,15,13,12,9,8,7,5,1],ofExponents [19,18,15,14,13,11,7,4],ofExponents [18,17,16,15,11,10,8,7,4,3,1],ofExponents [19,17,16,14,13,10,9,7,6,5,4,3,2,1],ofExponents [19,16,15,13,12,11,10,9,6,5,4,2],ofExponents [19,13,7,1],ofExponents [19,15,14,13,11,9,8,6],ofExponents [15,12,11,8,6,5,4,3,1,0],ofExponents [19,17,15,13,11,9,8,6,3,1],ofExponents [19,17,15,14,13,12,11,8,7,1],ofExponents [19,13,12,10,8,7,6,5,4,1],ofExponents [19,16,15,12,10,9,8,7,1,0],ofExponents [19,15,14,12,9,7,4,3,1,0],ofExponents [1]]]

private def quotients : Fin 5 → List ((ZMod 2)[X]) := ![
  [ofExponents [1]],
  [ofExponents [],ofExponents [0],ofExponents [],ofExponents [0]],
  [ofExponents [],ofExponents [],ofExponents [2,0],ofExponents [4,1],ofExponents [2,0],ofExponents [4,1]],
  [ofExponents [],ofExponents [],ofExponents [],ofExponents [2],ofExponents [4,0],ofExponents [8,6,4,1],ofExponents [8,6,1,0],ofExponents [10,4,3,1,0],ofExponents [12,8,6,5,4,3,2],ofExponents [10,8,6,4,3],ofExponents [12,8,5,3,0],ofExponents [12,10,8,5,1,0],ofExponents [8,2,1,0],ofExponents [12,10,8,5,4,2,1]],
  [ofExponents [],ofExponents [],ofExponents [],ofExponents [],ofExponents [12,2,1],ofExponents [18,16,14,12,8,7,3,2,1,0],ofExponents [18,16,12,7,6,0],ofExponents [14,12,10,6,3,2],ofExponents [18,16,10,7,4,2,1],ofExponents [16,14,12,10,6,5,4,2,1],ofExponents [18,14,12,7,6,5],ofExponents [18,12,10,8,7,6,5,3,2,1],ofExponents [18,8,7,6,5,4,3,2],ofExponents [18,10,7,6,5,4,3,0],ofExponents [10,4,2,0],ofExponents [18,14,10,8,7,6,5,1],ofExponents [18,14,10,7,6,5,4,1],ofExponents [18,8,7,6,5,3,2,0],ofExponents [18,12,10,8,7,5,3,1],ofExponents [18,10,7,5,3,2,0]]]

private def tests : Fin 5 → Finset ℕ := ![∅,{2},{2,3},{2,7},{4,10}]

private def bezoutLeft (i : Fin 5) (m : ℕ) : (ZMod 2)[X] :=
  match i.val,m with
  | 1,2 => ofExponents []
  | 2,2 => ofExponents [0]
  | 2,3 => ofExponents [3,2,0]
  | 3,2 => ofExponents [3,2,0]
  | 3,7 => ofExponents [10,9,8,4,2,0]
  | 4,4 => ofExponents [15,13,12,10,9,8,7,5,4,3,0]
  | 4,10 => ofExponents [18,16,15,14,12,10,7,6,4,2,1,0]
  | _,_ => 0

private def bezoutRight (i : Fin 5) (m : ℕ) : (ZMod 2)[X] :=
  match i.val,m with
  | 1,2 => ofExponents [0]
  | 2,2 => ofExponents [2,0]
  | 2,3 => ofExponents [4,2,1]
  | 3,2 => ofExponents [13,12,9,5,4,1]
  | 3,7 => ofExponents [12,11,10,9,8,6,4,3,0]
  | 4,4 => ofExponents [19,17,16,14,13,12,11,6,4,3,2,0]
  | 4,10 => ofExponents [19,15,14,13,11,10,9,6,5,4,3,2,1]
  | _,_ => 0

private theorem initial_checked : ∀ i : Fin 5, (remainders i).getD 0 0=X := by
  intro i
  fin_cases i <;> simp [remainders, ofExponents]

private theorem final_checked : ∀ i : Fin 5, (remainders i).getD (degree i) 0=X := by
  intro i
  fin_cases i <;> simp [remainders, degree, ofExponents]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem steps_checked : ∀ (i : Fin 5) (j : Fin (degree i)),
    ((remainders i).getD j.val 0)^2 =
      polynomial i * (quotients i).getD j.val 0 + (remainders i).getD (j.val+1) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polynomial, remainders, quotients, List.getD, ofExponents] <;>
    ring_nf <;> reduce_mod_char

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bezout_checked : ∀ (i : Fin 5) (m : Fin (degree i+1)), m.val∈tests i →
    bezoutLeft i m.val * polynomial i +
      bezoutRight i m.val * ((remainders i).getD m.val 0-X)=1 := by
  intro i m
  fin_cases i <;> fin_cases m <;>
    norm_num [tests, bezoutLeft, bezoutRight, polynomial, remainders, List.getD, ofExponents] <;>
    ring_nf <;> reduce_mod_char

private theorem test_bounds (i : Fin 5) (m : ℕ) (hm : m∈tests i) : m≤degree i := by
  fin_cases i <;> simp [tests,degree] at hm ⊢ <;> omega

private theorem divisor_cover_checked : ∀ (i : Fin 5) (d : Fin (degree i+1)),
    0<d.val → d.val≤degree i/2 → d.val∣degree i →
      ∃ m : Fin (degree i+1), m.val∈tests i ∧ d.val∣m.val := by
  decide +kernel

/-- Kernel-checked Frobenius and Bezout certificates prove all five factors irreducible. -/
theorem irreducible (i : Fin 5) : Irreducible (polynomial i) := by
  have hpos : 0<degree i := (by decide : ∀ i : Fin 5, 0<degree i) i
  have hs : ∀ j<degree i, ((remainders i).getD j 0)^2=
      polynomial i * (quotients i).getD j 0 + (remainders i).getD (j+1) 0 :=
    fun j hj => steps_checked i ⟨j,hj⟩
  apply irreducible_of_frobenius_tests (polynomial i) (degree i) hpos (monic i) (natDegree i) (tests i)
  · have hh := reduction_divides (polynomial i) (degree i)
      (fun j => (remainders i).getD j 0) (fun j => (quotients i).getD j 0) (initial_checked i) hs
    simpa only [Nat.card_zmod,final_checked] using hh
  · intro m hm
    have hmn := test_bounds i m hm
    have hh := reduction_divides (polynomial i) m
      (fun j => (remainders i).getD j 0) (fun j => (quotients i).getD j 0) (initial_checked i)
      (fun j hj => hs j (hj.trans_le hmn))
    have hc : IsCoprime (polynomial i) ((remainders i).getD m 0-X) :=
      ⟨bezoutLeft i m,bezoutRight i m,bezout_checked i ⟨m,by omega⟩ hm⟩
    simpa only [Nat.card_zmod] using coprime_of_reduction (polynomial i) _ m hh hc
  · intro d hdpos hsmall hdiv
    obtain ⟨m,hm,hdm⟩ := divisor_cover_checked i ⟨d,by omega⟩ hdpos hsmall hdiv
    exact ⟨m.val,hm,hdm⟩


/-- The five spectral factors are pairwise coprime. -/
theorem pairwise_isCoprime : Pairwise fun i j : Fin 5 =>
    IsCoprime (polynomial i) (polynomial j) := by
  intro i j hij
  apply (irreducible i).coprime_iff_not_dvd.mpr
  intro hdvd
  have heq := Polynomial.eq_of_monic_of_associated (monic i) (monic j)
    ((irreducible i).associated_of_dvd (irreducible j) hdvd)
  have hdeg : degree i=degree j := by simpa only [natDegree] using congrArg Polynomial.natDegree heq
  have hinj : Function.Injective degree := by decide +kernel
  exact hij (hinj hdeg)

end BinaryEndpointInduction.SpectralPolynomials
