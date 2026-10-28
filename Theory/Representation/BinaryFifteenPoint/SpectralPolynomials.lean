module
public import Theory.Representation.BinaryEndpointInduction.SpectralPolynomials

/-!
# The five primary factors of a fifteen-cycle over the binary field

Explicit divisibility and Bezout identities prove irreducibility. The
three quartics remain distinct, so all five factors are pairwise coprime.
-/
@[expose] public noncomputable section
open Polynomial
namespace BinaryFifteenPoint.SpectralPolynomials

/-- Primary-block dimensions of the literal fifteen-cycle. -/
def degree : Fin 5 → ℕ := ![1,2,4,4,4]
/-- All distinct irreducible factors of X^15-1 over F2. -/
def polynomial : Fin 5 → (ZMod 2)[X] := ![X+1, X^2+X+1, X^4+X+1, X^4+X^3+1, X^4+X^3+X^2+X+1]

theorem natDegree (i : Fin 5) : (polynomial i).natDegree=degree i := by
  fin_cases i <;> dsimp [polynomial,degree] <;> compute_degree!

theorem monic (i : Fin 5) : (polynomial i).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [natDegree]
  fin_cases i <;> dsimp [polynomial,degree] <;> compute_degree!

private def quotient : Fin 5 → (ZMod 2)[X] := ![X, X^2+X, X^12+X^9+X^8+X^6+X^4+X^3+X^2+X, X^12+X^11+X^10+X^9+X^7+X^5+X^4+X, X^12+X^11+X^7+X^6+X^2+X]
private def testDegree : Fin 5 → ℕ := ![0,1,2,2,2]
private def tests (i : Fin 5) : Finset ℕ := if i=0 then ∅ else {testDegree i}
private def bezoutLeft : Fin 5 → (ZMod 2)[X] := ![0, 1, 1, X^3+X^2+1, X^3+X+1]
private def bezoutRight : Fin 5 → (ZMod 2)[X] := ![0, 1, 1, X^3+X, X^3+X^2]

private theorem full_check (i : Fin 5) :
    X^(2^degree i)-X=polynomial i*quotient i := by
  fin_cases i <;> norm_num [degree,polynomial,quotient] <;> ring_nf <;> reduce_mod_char

private theorem bezout_check (i : Fin 5) (hi : i≠0) :
    bezoutLeft i*polynomial i+bezoutRight i*(X^(2^testDegree i)-X)=1 := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    dsimp [bezoutLeft,bezoutRight,polynomial,testDegree]
    ring_nf
    reduce_mod_char

/-- All five displayed primary factors are irreducible over F2. -/
theorem irreducible (i : Fin 5) : Irreducible (polynomial i) := by
  apply BinaryEndpointInduction.SpectralPolynomials.irreducible_of_frobenius_tests
    (polynomial i) (degree i) ((by decide : ∀ j : Fin 5, 0<degree j) i)
    (monic i) (natDegree i) (tests i)
  · rw [Nat.card_zmod]
    exact ⟨quotient i,full_check i⟩
  · intro m hm
    have hi : i≠0 := by intro he; simp [tests,he] at hm
    have he : m=testDegree i := by simpa only [tests,if_neg hi,Finset.mem_singleton] using hm
    subst m
    rw [Nat.card_zmod]
    exact ⟨bezoutLeft i,bezoutRight i,bezout_check i hi⟩
  · intro d hd hsmall hdiv
    have hc : ∀ (j : Fin 5) (n : Fin (degree j+1)),
        0<n.val → n.val≤degree j/2 → n.val∣degree j →
          ∃ m : Fin (degree j+1), m.val∈tests j ∧ n.val∣m.val := by decide +kernel
    obtain ⟨m,hm,hdm⟩ := hc i ⟨d,by omega⟩ hd hsmall hdiv
    exact ⟨m.val,hm,hdm⟩

private theorem coefficient_profiles (i : Fin 5) :
    ((polynomial i).coeff 1,(polynomial i).coeff 2)=
      ((![1,1,1,0,1] i : ZMod 2),(![0,1,0,0,1] i : ZMod 2)) := by
  fin_cases i <;> norm_num [polynomial,Polynomial.coeff_one,Polynomial.coeff_X]

/-- Distinct primary factors give the polynomial projections used by the lattice proof. -/
theorem pairwise_isCoprime : Pairwise fun i j : Fin 5 =>
    IsCoprime (polynomial i) (polynomial j) := by
  intro i j hij
  apply (irreducible i).coprime_iff_not_dvd.mpr
  intro hdvd
  have heq := Polynomial.eq_of_monic_of_associated (monic i) (monic j)
    ((irreducible i).associated_of_dvd (irreducible j) hdvd)
  have hd : degree i=degree j := by simpa only [natDegree] using congrArg Polynomial.natDegree heq
  have hc := congrArg (fun p : (ZMod 2)[X] => (p.coeff 1,p.coeff 2)) heq
  rw [coefficient_profiles,coefficient_profiles] at hc
  have hinj : Function.Injective (fun k : Fin 5 =>
      (degree k,((![1,1,1,0,1] k : ZMod 2),(![0,1,0,0,1] k : ZMod 2)))) := by decide +kernel
  exact hij (hinj (Prod.ext hd hc))

end BinaryFifteenPoint.SpectralPolynomials
