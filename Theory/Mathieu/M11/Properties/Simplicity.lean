module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Sylow
public import Theory.Mathieu.M11.Properties.Order

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open MulAction
open scoped Pointwise

private theorem m11GeneratorAInM11_ne_one : m11GeneratorAInM11 ≠ 1 := by
  intro h
  have h' := congrArg (fun g : M11 => (g : Equiv.Perm (Fin 11))) h
  have h'' := congrArg (fun g : Equiv.Perm (Fin 11) => g (2 : Fin 11)) h'
  have h''a : (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) 2 = 2 := by
    change (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) 2 = 2 at h''
    exact h''
  have : (10 : Fin 11) = 2 := by
    rw [show (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) = m11GeneratorA by rfl] at h''a
    simp [m11GeneratorA, Equiv.swap_apply_def] at h''a
  exact (by decide +kernel : (10 : Fin 11) ≠ 2) this

private noncomputable def m11Standard11 : M11 := m11GeneratorAInM11 * m11GeneratorBInM11

private theorem m11Standard11_order : orderOf m11Standard11 = 11 := by
  rw [← Subgroup.orderOf_coe m11Standard11]
  change orderOf (m11GeneratorA * m11GeneratorB) = 11
  exact m11GeneratorAB_order

private noncomputable def m11ConjugateStandard11 : M11 :=
  m11GeneratorAInM11 * m11Standard11 * (m11GeneratorAInM11)⁻¹

private theorem m11GeneratorA_word :
    m11GeneratorAInM11 =
      m11Standard11 * m11Standard11 * m11ConjugateStandard11⁻¹ *
        m11Standard11 * m11Standard11 * m11ConjugateStandard11⁻¹ *
        m11ConjugateStandard11⁻¹ * m11Standard11 *
        m11ConjugateStandard11⁻¹ * m11Standard11 := by
  apply Subtype.ext
  have hA : (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) = m11GeneratorA := rfl
  simp only [m11Standard11, m11ConjugateStandard11, hA]
  ext x
  fin_cases x <;> rfl

private theorem m11GeneratorB_word :
    m11GeneratorBInM11 =
      m11Standard11 * m11Standard11 * m11ConjugateStandard11⁻¹ *
        m11ConjugateStandard11⁻¹ * m11Standard11 *
        m11ConjugateStandard11⁻¹ * m11Standard11 *
        m11ConjugateStandard11 * m11ConjugateStandard11 := by
  apply Subtype.ext
  simp only [m11Standard11, m11ConjugateStandard11]
  ext x
  fin_cases x <;> rfl

public theorem m11_isSimpleGroup : IsSimpleGroup M11 := by
  classical
  let : MulAction.IsPreprimitive M11 (Fin 11) :=
    MulAction.IsPreprimitive.of_prime_card (by simpa using Nat.prime_eleven)
  let : Nontrivial M11 := ⟨⟨m11GeneratorAInM11, 1, m11GeneratorAInM11_ne_one⟩⟩
  apply IsSimpleGroup.mk
  intro N hN
  let : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  have hfix : MulAction.fixedPoints N (Fin 11) ≠ Set.univ := by
    intro h
    apply hNbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.fixedPoints N (Fin 11) := by
      rw [h]
      exact Set.mem_univ x
    have hxn := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
    change (n : Equiv.Perm (Fin 11)) x = x at hxn
    exact hxn
  let : MulAction.IsPretransitive N (Fin 11) :=
    (inferInstance : MulAction.IsQuasiPreprimitive M11 (Fin 11)).isPretransitive_of_normal hfix
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer N (0 : Fin 11))
  rw [MulAction.index_stabilizer_of_transitive N (0 : Fin 11), Nat.card_fin] at hmul
  have h11dvd : 11 ∣ Nat.card N := by
    refine ⟨Nat.card (MulAction.stabilizer N (0 : Fin 11)), ?_⟩
    simpa [Nat.mul_comm] using hmul.symm
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' 11 h11dvd
  let H : Subgroup M11 := (Subgroup.zpowers x).map N.subtype
  have hHleN : H ≤ N := by
    intro g hg
    rcases hg with ⟨y, hy, rfl⟩
    exact y.property
  have hHcard : Nat.card H = 11 := by
    dsimp [H]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective N),
      Nat.card_zpowers, hxorder]
  have hHp : Nat.card H = 11 ^ 1 := by
    rw [hHcard]
    norm_num
  obtain ⟨Q, hHQ⟩ := (IsPGroup.of_card hHp).exists_le_sylow
  have hpadic : padicValNat 11 7920 = 1 := by
    have hval0 : padicValNat 11 720 = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hle : 1 ≤ padicValNat 11 720 := hpos
      have hdvd : 11 ^ 1 ∣ 720 :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) (by norm_num)).mpr hle
      norm_num at hdvd
    rw [show (7920 : ℕ) = 11 * 720 by norm_num,
      padicValNat_base_mul (by norm_num) (by norm_num), hval0]
  have hQcard : Nat.card Q = 11 := by
    rw [Sylow.card_eq_multiplicity, m11_order]
    rw [Nat.factorization_def _ Nat.prime_eleven, hpadic]
    norm_num
  have hHQeq : H = (Q : Subgroup M11) :=
    Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHcard, hQcard])
  let P : Sylow 11 M11 := Sylow.ofCard (Subgroup.zpowers m11Standard11) (by
    rw [Nat.card_zpowers, m11Standard11_order, m11_order]
    rw [Nat.factorization_def _ Nat.prime_eleven, hpadic]
    norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M11 Q P
  have hQleN : (Q : Subgroup M11) ≤ N := by
    rw [← hHQeq]
    exact hHleN
  have hPleN : (P : Subgroup M11) ≤ N := by
    rw [← hg]
    change MulAut.conj g • (Q : Subgroup M11) ≤ N
    rintro _ ⟨k, hk, rfl⟩
    exact hN.conj_mem k (hQleN hk) g
  have hpN : m11Standard11 ∈ N := by
    have hpP : m11Standard11 ∈ (P : Subgroup M11) := by
      change m11Standard11 ∈ Subgroup.zpowers m11Standard11
      exact Subgroup.mem_zpowers m11Standard11
    exact hPleN hpP
  let K : Subgroup M11 := Subgroup.normalClosure ({m11Standard11} : Set M11)
  have hpK : m11Standard11 ∈ K := Subgroup.subset_normalClosure (by simp)
  have hqK : m11ConjugateStandard11 ∈ K := by
    change m11GeneratorAInM11 * m11Standard11 *
      (m11GeneratorAInM11)⁻¹ ∈ K
    exact Subgroup.normalClosure_normal.conj_mem m11Standard11 hpK
      m11GeneratorAInM11
  have hqInvK : m11ConjugateStandard11⁻¹ ∈ K := K.inv_mem hqK
  have hAK : m11GeneratorAInM11 ∈ K := by
    rw [m11GeneratorA_word]
    simpa only [mul_assoc] using
      K.mul_mem
        (K.mul_mem (K.mul_mem hpK hpK) hqInvK)
        (K.mul_mem
          (K.mul_mem hpK hpK)
          (K.mul_mem hqInvK
            (K.mul_mem hqInvK
              (K.mul_mem hpK
                (K.mul_mem hqInvK hpK)))))
  have hBK : m11GeneratorBInM11 ∈ K := by
    rw [m11GeneratorB_word]
    simpa only [mul_assoc] using
      K.mul_mem
        (K.mul_mem (K.mul_mem hpK hpK) hqInvK)
        (K.mul_mem hqInvK
          (K.mul_mem hpK
            (K.mul_mem hqInvK
              (K.mul_mem hpK (K.mul_mem hqK hqK)))))
  have hKtop : K = ⊤ := by
    apply top_unique
    rw [← m11_generators_closure_eq_top]
    exact (Subgroup.closure_le K).mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hAK
      · exact hBK)
  apply top_unique
  rw [← hKtop]
  apply Subgroup.normalClosure_le_normal
  intro z hz
  rcases hz with rfl
  exact hpN

end Sporadic.Mathieu
