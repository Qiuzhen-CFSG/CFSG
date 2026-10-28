module
public import Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Mathlib.GroupTheory.Schreier

/-!
# Three Sylow Frattini generators for Mersenne unitary four-space

In U₂(p), with p+1 a power of two, the norm-one diagonal matrices and
coordinate swap generate a Sylow subgroup. One diagonal generator and
the swap generate it, so its Frattini quotient has order at most four.
The determinant-one two-block embedding in SU₄ adds one swap and has
odd index. Thus every SU₄ Sylow Frattini quotient has order at most eight.
Orthonormal transport and the actual map into PGL give the same bound
for the stored projective Hermitian group.

This excludes its GL₄(2) outer section in Aschbacher--Smith 4.4.10--11
and 12.1.9, printed pp.621,793. The diagonal matrices use the shared
ABG II.2 construction in `GL2.DiagonalSwap`; the unitary count uses the
licensed ATLAS support imported by `OddFrattiniSixteen`.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
namespace Theory.SpecificGroups.ClassicalUnitary.MersenneFrattini
open GeneralLinearGroup OddFrattiniSixteen
variable {F : Type*} [Field F] [Finite F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U₂" => HermitianForm.unitarySubgroup (form σ hσ 2)
local notation "C" => OddFourRanks.normOne (form σ hσ 4)

private theorem pair_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (a b : P) (hg : closure ({a,b} : Set P) = ⊤) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  classical
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hr : Group.rank P ≤ 2 := (Group.rank_le (S := {a,b}) (by simpa using hg)).trans
    (Finset.card_insert_le _ _ |>.trans (by simp))
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini P))
    (QuotientGroup.mk'_surjective _)).trans hr
  have hd := card_dvd_exponent_pow_rank' (P ⧸ frattini P)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ frattini P)))
  exact (Nat.le_of_dvd (by positivity) hd).trans
    (show 2 ^ Group.rank (P ⧸ frattini P) ≤ 4 by
      exact Nat.pow_le_pow_right (by decide) hq)

omit [Finite F] in
private theorem diagonal_unitary (u v : C) : diagonalPair F (u.val,v.val) ∈ U₂ := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change (form σ hσ 2).conjTranspose (diagonalPair F (u.val,v.val)).val * 1 *
    (diagonalPair F (u.val,v.val)).val = 1
  rw [mul_one]
  have hu := OddFourRanks.normOne_norm (form σ hσ 4) u
  have hv := OddFourRanks.normOne_norm (form σ hσ 4) v
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPair,HermitianForm.conjTranspose,form,Matrix.mul_apply,Fin.sum_univ_two]
  · exact hu
  · exact hv

omit [Finite F] in
private theorem swap_unitary : coordinateSwap F ∈ U₂ := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateSwap,HermitianForm.conjTranspose,form,Matrix.mul_apply,Fin.sum_univ_two]

omit [Finite F] in
private theorem diagonal_swap_le (z : C) : diagonalSwapSubgroup F z.val ≤ U₂ := by
  apply (closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact diagonal_unitary σ hσ z 1
  · exact diagonal_unitary σ hσ 1 z
  · exact swap_unitary σ hσ

omit [Finite F] in
private theorem diagonal_swap_pair (z : C) :
    closure ({diagonalPair F (z.val,1),coordinateSwap F} : Set (GL (Fin 2) F)) =
      diagonalSwapSubgroup F z.val := by
  apply le_antisymm
  · exact closure_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *; tauto)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · rw [←coordinateSwap_conj_diagonalPair F z.val 1]
      exact mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
        (inv_mem (subset_closure (by simp)))
    · exact subset_closure (by simp)

/-- The diagonal norm-one matrices and their swap supply a two-generator
Sylow subgroup of the actual unitary two-space at a Mersenne prime. -/
theorem unitary_two_frattini_le {p : ℕ} [Fact p.Prime]
    (hm : ∃ k : ℕ, p+1 = 2^k) (hc : Nat.card F = p^2) (hj : ∀ x, σ x = x^p)
    (P : Sylow 2 U₂) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  obtain ⟨k,hk⟩ := hm
  have hp := (Fact.out : p.Prime).two_le
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> norm_num at hk <;> omega
  have ho : Odd p := by
    have he : Even (2^k) := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega : k ≠ 0)
    rw [←hk] at he
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)
  have hC := norm_one_card σ hσ (by omega : 1 ≤ p) hc hj
  obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hz' : orderOf z.val = 2^k := by rw [Subgroup.orderOf_coe,hz,hC,hk]
  let H := diagonalSwapSubgroup F z.val
  let R := H.subgroupOf U₂
  let e : R ≃* H := subgroupOfEquivOfLe (diagonal_swap_le σ hσ z)
  have hR : Nat.card R = 2^(2*k+1) := by
    rw [Nat.card_congr e.toEquiv,diagonalSwapSubgroup_card,hz']
    rw [show 2*k+1=k*2+1 by omega, pow_add,pow_mul,pow_one]
    ring
  have htwo : IsPGroup 2 R := IsPGroup.of_card hR
  have hind : Odd R.index := by
    have hG := unitary_two_card σ hσ ho hc hj
    have he := R.card_mul_index
    rw [hR,hG] at he
    have hpow : 2^k = 2 * 2^(k-1) := by rw [←pow_succ',Nat.sub_add_cancel (by omega)]
    have hfac : p^2-1 = (p-1)*(p+1) := by
      have ht : (p-1)*(p+1)+1 = p^2 := by
        have hp' : p-1+1=p := by omega
        nlinarith
      omega
    have heq : 2 * R.index = p*(p-1) := by
      have he' : 2^(2*k) * (2*R.index) = 2^(2*k) * (p*(p-1)) := by
        calc
          _ = 2^(2*k+1)*R.index := by rw [pow_succ]; ring
          _ = _ := he
          _ = _ := by rw [hfac,hk,show 2*k=k*2 by omega,pow_mul]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(2*k)) he'
    have hidx : R.index = p*(2^(k-1)-1) := by
      have hp2 : 1 ≤ 2^(k-1) := Nat.one_le_pow _ _ (by decide)
      have hpminus : p-1 = 2*(2^(k-1)-1) := by omega
      rw [hpminus] at heq
      nlinarith
    rw [hidx]
    have he : Even (2^(k-1)) := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
    exact ho.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide)) he (by decide))
  let S : Sylow 2 U₂ := htwo.toSylow hind.not_two_dvd_nat
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S)]
  change Nat.card (R ⧸ frattini R) ≤ 4
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr e]
  let a : H := ⟨diagonalPair F (z.val,1),subset_closure (by simp)⟩
  let b : H := ⟨coordinateSwap F,subset_closure (by simp)⟩
  apply pair_frattini_le_four (htwo.of_surjective e.toMonoidHom e.surjective) a b
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,H.range_subtype,
    Set.image_insert_eq,Set.image_singleton]
  exact diagonal_swap_pair σ hσ z

/-- The original SU₄ Sylow group has at most three Frattini generators. -/
theorem special_frattini_le (J : HermitianForm 4 F) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hm : ∃ k : ℕ, p+1 = 2^k)
    (hc : Nat.card F = p^2) (hj : ∀ x, J.conj x = x^p)
    (P : Sylow 2 J.specialSubgroup) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  obtain ⟨basis,e,ep,hbasis,he,hep⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J p Fact.out hc hj
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
    (e.subgroupMap (P : Subgroup J.specialSubgroup))]
  exact identity_frattini_le_of_unitary_two_bound J.conj J.conj_involutive ho hc hj 4
    (unitary_two_frattini_le J.conj J.conj_involutive hm hc hj)
    (P.mapSurjective e.surjective)

/-- The literal SU-to-PGL image inherits the three-generator Sylow bound. -/
theorem projective_frattini_le (J : HermitianForm 4 F) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hm : ∃ k : ℕ, p+1 = 2^k)
    (hc : Nat.card F = p^2) (hj : ∀ x, J.conj x = x^p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 8 := by
  exact Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (ProjectiveKernel.project J) (ProjectiveKernel.project_surjective J)
    (special_frattini_le J ho hm hc hj) P

end Theory.SpecificGroups.ClassicalUnitary.MersenneFrattini
