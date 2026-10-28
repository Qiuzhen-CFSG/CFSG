module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Collection
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.FinCases

/-!
# The defining-prime index of the positive SU₄ subgroup

The four positive root groups generate a Sylow subgroup for the defining
prime. A prime-power overgroup has a nonzero fixed vector on the natural
module. Two explicit short roots force it to fix the first coordinate vector.
A second fixed-vector argument on the middle block, using a nonzero trace-zero
long-root parameter, forces the remaining diagonal entries and lower entries.
The unitary equations then recover the exact collected root word.

Thus the literal positive subgroup has index prime to q. Compatible root
lifts consequently exclude q from a perfect central cover's kernel by the
proved section and transfer theorem. Their existence remains a separate
obligation. The index argument is valid for every prime q; it does not use
the Mersenne or quasisimplicity hypotheses of the source application.

Source: the defining-prime ingredient for Aschbacher--Smith I.1.4(3), printed
p.408 of `refs/quasithin.pdf`, and GLS3 §6.1. The root coordinates use the
basis (e₁,e₂,f₁,f₂), with upper triangular order (0,1,3,2).
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime

variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F)
local notation "G" => HyperbolicSU J

private def pointLocal : Subgroup G :=
  (MulAction.stabilizer (GL (Fin 4) F) (![1,0,0,0] : Fin 4 → F)).comap
    (hyperbolicForm J).specialSubgroup.subtype

private theorem mem_pointLocal (a : G) : a ∈ pointLocal J ↔
    a.val.val 0 0 = 1 ∧ a.val.val 1 0 = 0 ∧
      a.val.val 2 0 = 0 ∧ a.val.val 3 0 = 0 := by
  change a.val • (![1,0,0,0] : Fin 4 → F) = _ ↔ _
  change a.val.val.mulVec (![1,0,0,0]) = _ ↔ _
  simp [mulVec, dotProduct, Fin.sum_univ_succ, funext_iff,
    Fin.forall_fin_succ]

private theorem opposite_row (a : G) (ha : a ∈ pointLocal J) :
    a.val.val 2 0 = 0 ∧ a.val.val 2 1 = 0 ∧
      a.val.val 2 2 = 1 ∧ a.val.val 2 3 = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := (mem_pointLocal J a).mp ha
  have hu := a.property.1
  change (hyperbolicForm J).conjTranspose a.val.val * gram * a.val.val = gram at hu
  have h0j := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 0) hu
  have h1j := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hu
  have h2j := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hu
  have h3j := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hu
  simp [hyperbolicForm, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h0,h1,h3] at h0j h1j h2j h3j
  rw [h2] at h1j h2j h3j
  have h1j' : a.val.val 2 1 = 0 := by simpa using h1j
  have h2j' : a.val.val 2 2 = 1 := by simpa using h2j
  have h3j' : a.val.val 2 3 = 0 := by simpa using h3j
  exact ⟨h2, h1j', h2j', h3j'⟩

private def blockMatrix : pointLocal J →* Matrix (Fin 2) (Fin 2) F where
  toFun a := !![a.val.val.val 1 1, a.val.val.val 1 3;
    a.val.val.val 3 1, a.val.val.val 3 3]
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    obtain ⟨_,a10,a20,a30⟩ := (mem_pointLocal J a.val).mp a.property
    obtain ⟨_,b21,b22,b23⟩ := opposite_row J b.val b.property
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, a10,a30,b21,b23]

private theorem block_det_ne_zero (a : pointLocal J) :
    (blockMatrix J a).det ≠ 0 := by
  intro hdet
  have hm : blockMatrix J (a * a⁻¹) = blockMatrix J a * blockMatrix J a⁻¹ :=
    (blockMatrix J).map_mul _ _
  have hone : blockMatrix J a * blockMatrix J a⁻¹ = 1 := by
    rw [← hm]
    simp
  have hd := congrArg Matrix.det hone
  rw [Matrix.det_mul, hdet, zero_mul] at hd
  simp at hd

private def blockGL : pointLocal J →* GL (Fin 2) F where
  toFun a := GeneralLinearGroup.mkOfDetNeZero (blockMatrix J a) (block_det_ne_zero J a)
  map_one' := by apply Units.ext; exact (blockMatrix J).map_one
  map_mul' a b := by apply Units.ext; exact (blockMatrix J).map_mul a b

variable [Finite F]

private theorem positive_le_pointLocal : positive J ≤ pointLocal J := by
  intro a ha
  obtain ⟨x,s,y,t,rfl⟩ := (mem_positive_iff J a).mp ha
  rw [mem_pointLocal, word_matrix]
  simp

private theorem overgroup_le_pointLocal {q : ℕ} [Fact q.Prime]
    (hcard : Nat.card F = q^2) (P : Subgroup G) (hP : IsPGroup q P)
    (hUP : positive J ≤ P) : P ≤ pointLocal J := by
  have hpV : q ∣ Nat.card (Fin 4 → F) := by
    rw [Nat.card_fun, hcard]
    exact (dvd_pow_self q (by decide : 2 ≠ 0)).trans
      (dvd_pow_self (q^2) (by simp))
  have hz : (0 : Fin 4 → F) ∈ MulAction.fixedPoints P (Fin 4 → F) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact smul_zero g
  obtain ⟨v,hv,hnv⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 4 → F) hpV hz
  have hfix := MulAction.mem_fixedPoints.mp hv
  have hx : shortRoot J (.ofAdd (1 : F)) ∈ P := hUP
    ((show (shortRoot J).range ≤ positive J from
      le_sup_left.trans (le_sup_left.trans le_sup_left)) ⟨.ofAdd 1,rfl⟩)
  have hy : middleRoot J (.ofAdd (1 : F)) ∈ P := hUP
    ((show (middleRoot J).range ≤ positive J from
      le_sup_right.trans le_sup_left) ⟨.ofAdd 1,rfl⟩)
  have hxf := hfix ⟨_,hx⟩
  have hyf := hfix ⟨_,hy⟩
  change shortMatrix J 1 *ᵥ v = v at hxf
  change middleMatrix J 1 *ᵥ v = v at hyf
  have hv1 : v 1 = 0 := by
    simpa [shortMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hxf 0
  have hv2 : v 2 = 0 := by
    simpa [middleMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hyf 1
  have hv3 : v 3 = 0 := by
    simpa [middleMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hyf 0
  have hv0 : v 0 ≠ 0 := by
    intro he
    apply hnv
    ext i
    fin_cases i <;> simp_all
  intro a ha
  have h := hfix ⟨a,ha⟩
  change a.val.val *ᵥ v = v at h
  have he (i : Fin 4) : a.val.val i 0 * v 0 = v i := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, hv1,hv2,hv3] using congrFun h i
  apply (mem_pointLocal J a).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hv0 (by simpa using he 0)
  · exact (mul_eq_zero.mp ((he 1).trans hv1)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 2).trans hv2)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 3).trans hv3)).resolve_right hv0

private theorem upper_entries_of_overgroup {q : ℕ} [Fact q.Prime]
    (hcard : Nat.card F = q^2) (α : traceZero J) (hα : (α : F) ≠ 0)
    (P : Subgroup G) (hP : IsPGroup q P) (hUP : positive J ≤ P)
    (a : P) : a.val.val.val 1 1 = 1 ∧ a.val.val.val 3 1 = 0 := by
  have hPL := overgroup_le_pointLocal J hcard P hP hUP
  let Q := P.subgroupOf (pointLocal J)
  let ρ := (blockGL J).comp Q.subtype
  let : MulAction Q (Fin 2 → F) := MulAction.compHom (Fin 2 → F) ρ
  have hQ : IsPGroup q Q := hP.comap_subtype
  have hpV : q ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun, hcard]
    exact (dvd_pow_self q (by decide : 2 ≠ 0)).trans
      (dvd_pow_self (q^2) (by simp))
  have hz : (0 : Fin 2 → F) ∈ MulAction.fixedPoints Q (Fin 2 → F) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    change (ρ g).val *ᵥ 0 = 0
    simp
  obtain ⟨v,hv,hnv⟩ :=
    hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hpV hz
  have hfix := MulAction.mem_fixedPoints.mp hv
  have hl : longRoot J (.ofAdd α) ∈ positive J :=
    (show (longRoot J).range ≤ positive J from le_sup_right) ⟨.ofAdd α,rfl⟩
  let l : Q := ⟨⟨longRoot J (.ofAdd α), positive_le_pointLocal J hl⟩, hUP hl⟩
  have he := hfix l
  change (!![1,(α:F);0,1] : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v at he
  have hv1 : v 1 = 0 := by
    have h : (α : F) * v 1 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun he 0
    exact (mul_eq_zero.mp h).resolve_left hα
  have hv0 : v 0 ≠ 0 := by
    intro he
    apply hnv
    ext i
    fin_cases i <;> simp_all
  let b : Q := ⟨⟨a.val, hPL a.property⟩, a.property⟩
  have h := hfix b
  change (!![a.val.val.val 1 1, a.val.val.val 1 3;
    a.val.val.val 3 1, a.val.val.val 3 3] : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v at h
  constructor
  · apply mul_right_cancel₀ hv0
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, hv1] using congrFun h 0
  · have h' : a.val.val.val 3 1 * v 0 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_succ, hv1] using congrFun h 1
    exact (mul_eq_zero.mp h').resolve_right hv0

private theorem mem_positive_of_local_entries (a : G) (ha : a ∈ pointLocal J)
    (h11 : a.val.val 1 1 = 1) (h31 : a.val.val 3 1 = 0) : a ∈ positive J := by
  obtain ⟨h00,h10,h20,h30⟩ := (mem_pointLocal J a).mp ha
  obtain ⟨_,h21,h22,h23⟩ := opposite_row J a ha
  have hu := a.property.1
  change (hyperbolicForm J).conjTranspose a.val.val * gram * a.val.val = gram at hu
  have h13u := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 3) hu
  have h33 : a.val.val 3 3 = 1 := by
    simpa [hyperbolicForm, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, h21,h23,h11,h31] using h13u
  have h12u := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hu
  have h22u := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 2) hu
  have h32u := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 3 2) hu
  have h33u := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 3 3) hu
  simp [hyperbolicForm, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h21,h22,h23,h31,h11,h33] at h12u h22u h32u h33u
  have ht : J.conj (a.val.val 1 3) = -a.val.val 1 3 :=
    eq_neg_of_add_eq_zero_right h33u
  have h32 : a.val.val 3 2 = -J.conj (a.val.val 0 1) :=
    eq_neg_of_add_eq_zero_right h12u
  let b : F := a.val.val 0 3 - a.val.val 0 1 * a.val.val 1 3
  have h12 : a.val.val 1 2 = -J.conj b := by
    dsimp only [b]
    rw [map_sub, map_mul, ht]
    rw [ht,h32] at h32u
    linear_combination h32u
  have hs : J.conj (a.val.val 0 2 + a.val.val 0 1 * J.conj b) =
      -(a.val.val 0 2 + a.val.val 0 1 * J.conj b) := by
    rw [h32,h12, map_neg,map_neg,J.conj_involutive,J.conj_involutive] at h22u
    rw [map_add,map_mul,J.conj_involutive]
    linear_combination h22u
  let s : traceZero J := ⟨a.val.val 0 2 + a.val.val 0 1 * J.conj b, hs⟩
  let t : traceZero J := ⟨a.val.val 1 3, ht⟩
  apply (mem_positive_iff J a).mpr
  refine ⟨a.val.val 0 1,s,b,t,?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [word_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s,t,h00,h10,h20,h30,h21,h22,h23,h11,h31,h33,h32,h12]
  dsimp [b]
  ring

/-- The literal positive root subgroup is a Sylow subgroup in defining characteristic. -/
def positiveSylow {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) : Sylow q G := by
  exact { positive J with
    isPGroup' := IsPGroup.of_card (card_positive_prime J hp hcard hconj)
    is_maximal' := by
      let : Fact q.Prime := ⟨hp⟩
      let := Fintype.ofFinite F
      let : CharP F q := charP_of_card_eq_prime_pow (f := 2) (by
        simpa only [Nat.card_eq_fintype_card] using hcard)
      obtain ⟨α,hα0,hα⟩ := exists_trace_zero J hcard hconj
      intro P hP hUP
      apply le_antisymm _ hUP
      intro a ha
      obtain ⟨h11,h31⟩ := upper_entries_of_overgroup J hcard ⟨α,hα⟩ hα0 P hP hUP ⟨a,ha⟩
      exact mem_positive_of_local_entries J a
        (overgroup_le_pointLocal J hcard P hP hUP ha) h11 h31 }

@[simp] theorem coe_positiveSylow {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    (positiveSylow J hp hcard hconj : Subgroup G) = positive J := rfl

/-- The positive subgroup has index prime to the defining prime. No cover,
Mersenne condition, or quasisimplicity assumption is needed. -/
theorem not_dvd_positive_index {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    ¬ q ∣ (positive J).index := by
  let : Fact q.Prime := ⟨hp⟩
  exact (positiveSylow J hp hcard hconj).not_dvd_index

/-- Transfer for the literal hyperbolic SU₄ cover. The section comes from
compatible lifted roots, and the prime-to-q index is discharged here. -/
theorem not_dvd_hyperbolic_kernel_of_positive_root_lifts {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (HyperbolicSU J))
    (L : PositiveRootLifts J f.toMonoidHom) :
    ¬ q ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact q.Prime := ⟨hp⟩
  obtain ⟨s,hs⟩ := L.exists_positive_section
  exact PerfectCentralCovering.not_dvd_card_kernel_of_section f (positive J)
    (not_dvd_positive_index J hp hcard hconj) s hs

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
