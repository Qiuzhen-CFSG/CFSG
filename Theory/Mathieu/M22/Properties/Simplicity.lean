module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.FinCases
public import Mathlib.GroupTheory.Sylow
public import Theory.Mathieu.M22.Properties.Order

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- Equality holds at every stage of the M22 stabilizer chain. -/
public theorem m22_stabilizer_cards :
    Nat.card m22Stab1 = 20160 ∧
      Nat.card m22Stab2 = 960 ∧
      Nat.card m22Stab3 = 48 ∧
      Nat.card m22Stab4 = 3 := by
  have h0 := m22_card_le_22_mul_stab1
  have h1 := m22_stab1_card_le_21_mul_stab2
  have h2 := m22_stab2_card_le_20_mul_stab3
  have h3 := m22_stab3_card_le_16_mul_stab4
  have h4 := m22_stab4_card_le_3_mul_stab5
  rw [m22_order] at h0
  rw [m22Stab5_card] at h4
  omega

public theorem m22Stab1_card : Nat.card m22Stab1 = 20160 :=
  m22_stabilizer_cards.1

public theorem m22Stab2_card : Nat.card m22Stab2 = 960 :=
  m22_stabilizer_cards.2.1

public theorem m22Stab3_card : Nat.card m22Stab3 = 48 :=
  m22_stabilizer_cards.2.2.1

public theorem m22Stab4_card : Nat.card m22Stab4 = 3 :=
  m22_stabilizer_cards.2.2.2

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open MulAction

private theorem m22_orbit_one_card :
    Nat.card (MulAction.orbit M22 (1 : Fin 22)) = 22 := by
  let : Fintype (MulAction.orbit M22 (1 : Fin 22)) := Fintype.ofFinite _
  let : Fintype m22Stab1 := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    M22 (1 : Fin 22)
  have hNat :
      Nat.card (MulAction.orbit M22 (1 : Fin 22)) *
          Nat.card m22Stab1 = Nat.card M22 := by
    simpa only [Nat.card_eq_fintype_card] using h
  rw [m22Stab1_card, m22_order] at hNat
  omega

public theorem m22_isPretransitive : IsPretransitive M22 (Fin 22) := by
  let : Fintype (MulAction.orbit M22 (1 : Fin 22)) := Fintype.ofFinite _
  rw [MulAction.isPretransitive_iff_orbit_eq_univ (1 : Fin 22)]
  apply (Set.eq_univ_iff_ncard _).2
  rw [← Set.fintypeCard_eq_ncard, ← Nat.card_eq_fintype_card]
  simpa using m22_orbit_one_card

private theorem m22Stab1_orbit_two_card :
    Nat.card (MulAction.orbit m22Stab1 (2 : Fin 22)) = 21 := by
  let : Fintype (MulAction.orbit m22Stab1 (2 : Fin 22)) := Fintype.ofFinite _
  let : Fintype m22Stab2 := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    m22Stab1 (2 : Fin 22)
  have hNat :
      Nat.card (MulAction.orbit m22Stab1 (2 : Fin 22)) *
          Nat.card m22Stab2 = Nat.card m22Stab1 := by
    simpa only [Nat.card_eq_fintype_card] using h
  rw [m22Stab2_card, m22Stab1_card] at hNat
  omega

private theorem m22Stab1_orbit_two_eq_compl :
    MulAction.orbit m22Stab1 (2 : Fin 22) = ({1} : Set (Fin 22))ᶜ := by
  let : Fintype (MulAction.orbit m22Stab1 (2 : Fin 22)) := Fintype.ofFinite _
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx1
    rcases MulAction.mem_orbit_iff.mp hx with ⟨g, hg⟩
    change m22Stab1Perm g 2 = x at hg
    exact (perm_apply_ne_of_ne_fixed (m22Stab1Perm g) (by decide +kernel)
      (m22Stab1_fix1 g)) (hg.trans hx1)
  · have horbit :
        (MulAction.orbit m22Stab1 (2 : Fin 22)).ncard = 21 := by
      rw [← Set.fintypeCard_eq_ncard, ← Nat.card_eq_fintype_card]
      exact m22Stab1_orbit_two_card
    have hcompl : (({1} : Set (Fin 22))ᶜ).ncard = 21 := by
      rw [Set.ncard_compl]
      simp
    rw [hcompl, horbit]

private theorem m22PointStabilizer_isPretransitive :
    IsPretransitive m22Stab1
      (SubMulAction.ofStabilizer M22 (1 : Fin 22)) := by
  constructor
  intro x y
  have hxOrbit : x.1 ∈ MulAction.orbit m22Stab1 (2 : Fin 22) := by
    rw [m22Stab1_orbit_two_eq_compl]
    exact x.2
  have hyOrbit : y.1 ∈ MulAction.orbit m22Stab1 (2 : Fin 22) := by
    rw [m22Stab1_orbit_two_eq_compl]
    exact y.2
  rcases MulAction.mem_orbit_iff.mp hxOrbit with ⟨gx, hgx⟩
  rcases MulAction.mem_orbit_iff.mp hyOrbit with ⟨gy, hgy⟩
  refine ⟨gy * gx⁻¹, ?_⟩
  apply Subtype.ext
  change (gy * gx⁻¹ : m22Stab1) • x.1 = y.1
  rw [mul_smul, ← hgx, inv_smul_smul]
  exact hgy

public theorem m22_isTwoPretransitive :
    IsMultiplyPretransitive M22 (Fin 22) 2 := by
  let : IsPretransitive M22 (Fin 22) := m22_isPretransitive
  have : IsPretransitive m22Stab1
      (SubMulAction.ofStabilizer M22 (1 : Fin 22)) :=
    m22PointStabilizer_isPretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M22) (α := Fin 22) (a := (1 : Fin 22)) (n := 1)).2
  exact MulAction.is_one_pretransitive_iff.mpr inferInstance

public theorem m22_isPreprimitive : IsPreprimitive M22 (Fin 22) :=
  MulAction.isPreprimitive_of_is_two_pretransitive m22_isTwoPretransitive

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


@[expose] public def m22GeneratorAInM22 : M22 :=
  ⟨m22GeneratorA, m22GeneratorA_mem_M22⟩

@[expose] public noncomputable def m22GeneratorBInM22 : M22 :=
  ⟨m22GeneratorB, m22GeneratorB_mem_M22⟩

@[expose] public noncomputable def m22Standard11 : M22 :=
  m22GeneratorAInM22 * m22GeneratorBInM22

public theorem m22Standard11_order : orderOf m22Standard11 = 11 := by
  rw [← Subgroup.orderOf_coe m22Standard11]
  change orderOf (m22GeneratorA * m22GeneratorB) = 11
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    intro x
    fin_cases x <;> rfl
  · intro h
    have h0 := congrArg (fun g : Equiv.Perm (Fin 22) => g (0 : Fin 22)) h
    change (16 : Fin 22) = 0 at h0
    exact (by decide +kernel : (16 : Fin 22) ≠ 0) h0

@[expose] public noncomputable def m22ConjugateStandard11 : M22 :=
  m22GeneratorAInM22 * m22Standard11 * m22GeneratorAInM22⁻¹

public theorem m22_generators_closure_eq_top :
    Subgroup.closure
      ({m22GeneratorAInM22, m22GeneratorBInM22} : Set M22) = ⊤ := by
  apply top_unique
  intro g _
  let K : Subgroup M22 :=
    Subgroup.closure
      ({m22GeneratorAInM22, m22GeneratorBInM22} : Set M22)
  have hAtlasLe : m22Atlas ≤ K.map M22.subtype := by
    rw [m22Atlas_eq_closure, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨m22GeneratorAInM22,
        Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨m22GeneratorBInM22,
        Subgroup.subset_closure (by simp), rfl⟩
  have hgAtlas : (g : Equiv.Perm (Fin 22)) ∈ m22Atlas := by
    rw [m22Atlas_eq_M22]
    exact g.property
  rcases hAtlasLe hgAtlas with ⟨x, hxK, hxg⟩
  have hxEq : x = g := Subtype.ext hxg
  simpa [hxEq] using hxK

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


public theorem m22GeneratorA_word :
    m22GeneratorAInM22 =
      m22Standard11 * m22Standard11 *
        m22ConjugateStandard11 * m22ConjugateStandard11 *
        m22Standard11 * m22Standard11 *
        m22ConjugateStandard11 * m22ConjugateStandard11 *
        m22Standard11 * m22Standard11 := by
  apply Subtype.ext
  simp only [m22Standard11, m22ConjugateStandard11,
    m22GeneratorAInM22, m22GeneratorBInM22]
  ext x
  fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


public theorem m22GeneratorB_word :
    m22GeneratorBInM22 =
      m22Standard11 *
        m22ConjugateStandard11 * m22ConjugateStandard11 *
        m22Standard11 * m22Standard11 *
        m22ConjugateStandard11 * m22ConjugateStandard11 *
        m22Standard11 * m22ConjugateStandard11⁻¹ := by
  apply Subtype.ext
  simp only [m22Standard11, m22ConjugateStandard11,
    m22GeneratorAInM22, m22GeneratorBInM22]
  ext x
  fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

public theorem m22_normalClosure_standard11_eq_top :
    Subgroup.normalClosure ({m22Standard11} : Set M22) = ⊤ := by
  let K : Subgroup M22 :=
    Subgroup.normalClosure ({m22Standard11} : Set M22)
  have hpK : m22Standard11 ∈ K :=
    Subgroup.subset_normalClosure (by simp)
  have hqK : m22ConjugateStandard11 ∈ K := by
    change m22GeneratorAInM22 * m22Standard11 *
      m22GeneratorAInM22⁻¹ ∈ K
    exact Subgroup.normalClosure_normal.conj_mem
      m22Standard11 hpK m22GeneratorAInM22
  have hqInvK : m22ConjugateStandard11⁻¹ ∈ K := K.inv_mem hqK
  have hAK : m22GeneratorAInM22 ∈ K := by
    rw [m22GeneratorA_word]
    simpa only [mul_assoc] using
      K.mul_mem hpK
        (K.mul_mem hpK
          (K.mul_mem hqK
            (K.mul_mem hqK
              (K.mul_mem hpK
                (K.mul_mem hpK
                  (K.mul_mem hqK
                    (K.mul_mem hqK
                      (K.mul_mem hpK hpK))))))))
  have hBK : m22GeneratorBInM22 ∈ K := by
    rw [m22GeneratorB_word]
    simpa only [mul_assoc] using
      K.mul_mem hpK
        (K.mul_mem hqK
          (K.mul_mem hqK
            (K.mul_mem hpK
              (K.mul_mem hpK
                (K.mul_mem hqK
                  (K.mul_mem hqK
                    (K.mul_mem hpK hqInvK)))))))
  apply top_unique
  rw [← m22_generators_closure_eq_top]
  exact (Subgroup.closure_le K).mpr (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hAK
    · exact hBK)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open MulAction
open scoped Pointwise

private theorem m22_padicValNat_eleven : padicValNat 11 443520 = 1 := by
  have hval0 : padicValNat 11 40320 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hle : 1 ≤ padicValNat 11 40320 := hpos
    have hdvd : 11 ^ 1 ∣ 40320 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) (by norm_num)).mpr hle
    norm_num at hdvd
  rw [show (443520 : ℕ) = 11 * 40320 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num), hval0]

public theorem m22Standard11_mem_of_normal_of_dvd_card
    (N : Subgroup M22) (hN : N.Normal) (h11dvd : 11 ∣ Nat.card N) :
    m22Standard11 ∈ N := by
  let : N.Normal := hN
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' 11 h11dvd
  let H : Subgroup M22 := (Subgroup.zpowers x).map N.subtype
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
  have hQcard : Nat.card Q = 11 := by
    rw [Sylow.card_eq_multiplicity, m22_order]
    rw [Nat.factorization_def _ Nat.prime_eleven,
      m22_padicValNat_eleven]
    norm_num
  have hHQeq : H = (Q : Subgroup M22) :=
    Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHcard, hQcard])
  let P : Sylow 11 M22 := Sylow.ofCard
    (Subgroup.zpowers m22Standard11) (by
      rw [Nat.card_zpowers, m22Standard11_order, m22_order]
      rw [Nat.factorization_def _ Nat.prime_eleven,
        m22_padicValNat_eleven]
      norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 Q P
  have hQleN : (Q : Subgroup M22) ≤ N := by
    rw [← hHQeq]
    exact hHleN
  have hPleN : (P : Subgroup M22) ≤ N := by
    rw [← hg]
    change MulAut.conj g • (Q : Subgroup M22) ≤ N
    rintro _ ⟨k, hk, rfl⟩
    exact hN.conj_mem k (hQleN hk) g
  have hpP : m22Standard11 ∈ (P : Subgroup M22) := by
    change m22Standard11 ∈ Subgroup.zpowers m22Standard11
    exact Subgroup.mem_zpowers m22Standard11
  exact hPleN hpP

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open MulAction
open scoped Pointwise

/-- The Mathieu group M22 is simple. -/
public theorem m22_isSimpleGroup : IsSimpleGroup M22 := by
  classical
  let : MulAction.IsPreprimitive M22 (Fin 22) := m22_isPreprimitive
  let : Nontrivial M22 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [m22_order]
    norm_num)
  apply IsSimpleGroup.mk
  intro N hN
  let : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  have hfix : MulAction.fixedPoints N (Fin 22) ≠ Set.univ := by
    intro h
    apply hNbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.fixedPoints N (Fin 22) := by
      rw [h]
      exact Set.mem_univ x
    have hxn := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
    change (n : Equiv.Perm (Fin 22)) x = x at hxn
    exact hxn
  let : MulAction.IsPretransitive N (Fin 22) :=
    (inferInstance : MulAction.IsQuasiPreprimitive M22 (Fin 22)).isPretransitive_of_normal hfix
  have hmul := Subgroup.card_mul_index
    (MulAction.stabilizer N (0 : Fin 22))
  rw [MulAction.index_stabilizer_of_transitive N (0 : Fin 22),
    Nat.card_fin] at hmul
  have h22dvd : 22 ∣ Nat.card N := by
    refine ⟨Nat.card (MulAction.stabilizer N (0 : Fin 22)), ?_⟩
    simpa [Nat.mul_comm] using hmul.symm
  have h11dvd : 11 ∣ Nat.card N :=
    dvd_trans (by norm_num) h22dvd
  have hpN : m22Standard11 ∈ N :=
    m22Standard11_mem_of_normal_of_dvd_card N hN h11dvd
  apply top_unique
  rw [← m22_normalClosure_standard11_eq_top]
  apply Subgroup.normalClosure_le_normal
  intro z hz
  rcases hz with rfl
  exact hpN

end Sporadic.Mathieu

