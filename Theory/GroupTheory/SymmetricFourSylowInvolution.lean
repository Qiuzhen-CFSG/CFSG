module

public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Mathlib.GroupTheory.Subgroup.Centralizer
public meta import Mathlib.Algebra.Group.End
import Mathlib.Tactic

/-!
# Core involutions in a symmetric-four Sylow subgroup

The elementary two-core has order four and lies in every Sylow two-subgroup,
which has order eight. A finite permutation calculation shows that every
nontrivial normal subgroup of S4 is self-centralizing. Thus some core element
is not centralized by the Sylow subgroup; its centralizer intersection contains
the abelian core and is proper in the Sylow subgroup, so has order four.
This is the local calculation in Stellmacher Section 11, case (I),
`refs/latex/stellmacher-n-group.tex`, lines 2082–2087.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem conjugate_centralizer_calculation :
    ∀ first : Equiv.Perm (Fin 4), first ≠ 1 →
      ∀ second : Equiv.Perm (Fin 4),
        (∀ conjugator : Equiv.Perm (Fin 4),
          (conjugator * first * conjugator⁻¹) * second =
            second * (conjugator * first * conjugator⁻¹)) →
        second = 1 ∨ ∃ conjugator : Equiv.Perm (Fin 4),
          second = conjugator * first * conjugator⁻¹ := by
  decide

private theorem normal_centralizer_le
    {K : Type*} [Group K] (equiv : K ≃* Equiv.Perm (Fin 4))
    (Q : Subgroup K) [Q.Normal] (first : K) (hfirst : first ∈ Q)
    (hne : first ≠ 1) : Subgroup.centralizer (Q : Set K) ≤ Q := by
  intro second hsecond
  have hcalc := conjugate_centralizer_calculation (equiv first)
    (by simpa using hne) (equiv second)
  have hcomm : ∀ conjugator : Equiv.Perm (Fin 4),
      (conjugator * equiv first * conjugator⁻¹) * equiv second =
        equiv second * (conjugator * equiv first * conjugator⁻¹) := by
    intro conjugator
    have hmem := Subgroup.Normal.conj_mem (inferInstance : Q.Normal)
      first hfirst (equiv.symm conjugator)
    have heq := Subgroup.mem_centralizer_iff.mp hsecond _ hmem
    simpa only [map_mul, map_inv, equiv.apply_symm_apply] using congrArg equiv heq
  rcases hcalc hcomm with hone | ⟨conjugator, hconj⟩
  · have : second = 1 := equiv.injective (by simpa using hone)
    exact this ▸ Q.one_mem
  · have : second = equiv.symm conjugator * first * (equiv.symm conjugator)⁻¹ := by
      apply equiv.injective
      simpa only [map_mul, map_inv, equiv.apply_symm_apply] using hconj
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance first hfirst _

public theorem symmetric_four_sylow_core_involution
    {K : Type*} [Group K] [Finite K] (T : Sylow 2 K)
    (hModel : Nonempty (K ≃* Equiv.Perm (Fin 4))) :
    ∃ x : K, x ∈ pCore 2 K ∧ orderOf x = 2 ∧
      Subgroup.centralizer ({x} : Set K) ⊓ (T : Subgroup K) = pCore 2 K ∧
      Nat.card (pCore 2 K) = 4 ∧ Nat.card T = 8 := by
  classical
  obtain ⟨equiv⟩ := hModel
  have hK : Nat.card K = 24 := by
    rw [Nat.card_congr equiv.toEquiv, Nat.card_eq_fintype_card]
    decide
  obtain ⟨helem, hcards⟩ := symmetric_four_model_twoCore_data (Or.inl ⟨equiv⟩)
  have hQ : Nat.card (pCore 2 K) = 4 := by
    rcases hcards with hcards | hcards
    · exact hcards.1
    · omega
  let := helem
  have hT : Nat.card T = 8 := by
    have hfac : Nat.factorization 24 2 = 3 := by
      have hzero : padicValNat 2 3 = 0 :=
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
      rw [Nat.factorization_def 24 Nat.prime_two,
        show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]
    rw [T.card_eq_multiplicity, hK, hfac]
    norm_num
  have hQT : pCore 2 K ≤ (T : Subgroup K) := pCore_isPGroup.le_sylow_of_normal T
  have hnontrivial : Nontrivial (pCore 2 K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let := hnontrivial
  obtain ⟨first, hfirst⟩ := exists_ne (1 : pCore 2 K)
  have hself := normal_centralizer_le equiv (pCore 2 K) first first.property
    (fun heq => hfirst (Subtype.ext heq))
  have hwitness : ∃ x ∈ pCore 2 K,
      ¬ (T : Subgroup K) ≤ Subgroup.centralizer ({x} : Set K) := by
    by_contra! hnone
    have hle : (T : Subgroup K) ≤ pCore 2 K := by
      apply le_trans ?_ hself
      intro second hsecond
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hnone x hx hsecond)).symm
    have := Subgroup.card_le_of_le hle
    change Nat.card T ≤ Nat.card (pCore 2 K) at this
    omega
  obtain ⟨x, hx, hnot⟩ := hwitness
  have hxne : x ≠ 1 := by
    rintro rfl
    exact hnot (fun second _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp))
  have hxpow : x ^ 2 = 1 := by
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (pCore 2 K)) ⟨x, hx⟩)
  have hxorder : orderOf x = 2 :=
    (Nat.dvd_prime (by decide)).mp (orderOf_dvd_of_pow_eq_one hxpow) |>.resolve_left
      (fun hone => hxne (orderOf_eq_one_iff.mp hone))
  let C := Subgroup.centralizer ({x} : Set K) ⊓ (T : Subgroup K)
  have hQC : pCore 2 K ≤ C := by
    refine le_inf ?_ hQT
    intro second hsecond
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨second, hsecond⟩ : pCore 2 K) ⟨x, hx⟩)
  have hCT : C ≤ (T : Subgroup K) := inf_le_right
  have hCne : C ≠ (T : Subgroup K) := by
    intro heq
    exact hnot (heq ▸ (inf_le_left : C ≤ Subgroup.centralizer ({x} : Set K)))
  have hCcard : Nat.card C = 4 := by
    have hlow := Subgroup.card_le_of_le hQC
    have hdiv := Subgroup.card_dvd_of_le hCT
    have hneq : Nat.card C ≠ 8 := by
      intro heq
      exact hCne (Subgroup.eq_of_le_of_card_ge hCT (by simp [heq, hT]))
    change Nat.card C ∣ Nat.card T at hdiv
    rw [hT] at hdiv
    have : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 4 ∨ Nat.card C = 8 := by
      have hsmall : ∀ divisor ∈ Nat.divisors 8,
          divisor = 1 ∨ divisor = 2 ∨ divisor = 4 ∨ divisor = 8 := by decide
      exact hsmall _ (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩)
    omega
  exact ⟨x, hx, hxorder, (Subgroup.eq_of_le_of_card_ge hQC (by omega)).symm, hQ, hT⟩
