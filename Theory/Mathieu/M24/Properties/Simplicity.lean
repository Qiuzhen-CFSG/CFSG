module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.Block
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.Simple
public import Theory.GroupAction.Stabilizer

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

open MulAction

private theorem m23SimplicityExtendHom_apply_embedded
    (g : M23) (i : Fin 23) :
    ((((m23SimplicityExtendHom g :
      MulAction.stabilizer M24 (24 : Fin 24)) : M24) :
        Equiv.Perm (Fin 24)) (m23PointEmbedding i)) =
      m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i) := by
  exact m23ExtendHom_apply_embedded g i

/-- The M24 point-24 stabilizer is transitive on the other twenty-three points. -/
public theorem m24PointStabilizer_isPretransitive :
    IsPretransitive (MulAction.stabilizer M24 (24 : Fin 24))
      (SubMulAction.ofStabilizer M24 (24 : Fin 24)) := by
  constructor
  intro x y
  obtain ⟨i, hi⟩ := m23PointEquiv.surjective x
  obtain ⟨j, hj⟩ := m23PointEquiv.surjective y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 i j
  refine ⟨m23SimplicityExtendHom g, ?_⟩
  apply Subtype.ext
  have hix : m23PointEmbedding i = x.1 := congrArg Subtype.val hi
  have hjy : m23PointEmbedding j = y.1 := congrArg Subtype.val hj
  change ((((m23SimplicityExtendHom g :
    MulAction.stabilizer M24 (24 : Fin 24)) : M24) :
      Equiv.Perm (Fin 24)) x.1) = y.1
  rw [← hix, ← hjy, m23SimplicityExtendHom_apply_embedded]
  exact congrArg m23PointEmbedding hg

private theorem m24_isTwoPretransitive :
    IsMultiplyPretransitive M24 (Fin 24) 2 := by
  have : IsPretransitive (MulAction.stabilizer M24 (24 : Fin 24))
      (SubMulAction.ofStabilizer M24 (24 : Fin 24)) :=
    m24PointStabilizer_isPretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M24) (α := Fin 24) (a := (24 : Fin 24)) (n := 1)).2
  exact MulAction.is_one_pretransitive_iff.mpr inferInstance

/-- The natural degree-24 action of M24 is primitive. -/
public theorem m24_isPreprimitive : IsPreprimitive M24 (Fin 24) :=
  MulAction.isPreprimitive_of_is_two_pretransitive m24_isTwoPretransitive

open MulAction
open scoped Pointwise

private theorem m24_sylow2_bounds_of_card_twenty_four
    (N : Subgroup M24) (hcardN : Nat.card N = 24)
    (P : Sylow 2 N) :
    Nat.card P = 8 ∧ Nat.card (Sylow 2 N) ≤ 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : Nat.factorization 24 2 = 3 := by
    have hzero : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 24 Nat.prime_two,
      show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]
  have hPcard : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity, hcardN, hfac]
    norm_num
  have hmul := Subgroup.card_mul_index (P : Subgroup N)
  rw [hPcard, hcardN] at hmul
  have hindex : P.index = 3 := by omega
  have hdvd : Nat.card (Sylow 2 N) ∣ 3 := by
    simpa [hindex] using Sylow.card_dvd_index P
  exact ⟨hPcard, Nat.le_of_dvd (by norm_num) hdvd⟩

private theorem m24_sylow3_bounds_of_card_twenty_four
    (N : Subgroup M24) (hcardN : Nat.card N = 24)
    (P : Sylow 3 N) :
    Nat.card P = 3 ∧ Nat.card (Sylow 3 N) ≤ 8 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : Nat.factorization 24 3 = 1 := by
    have hzero : padicValNat 3 8 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 24 Nat.prime_three,
      show (24 : ℕ) = 3 ^ 1 * 8 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hcardN, hfac]
    norm_num
  have hmul := Subgroup.card_mul_index (P : Subgroup N)
  rw [hPcard, hcardN] at hmul
  have hindex : P.index = 8 := by omega
  have hdvd : Nat.card (Sylow 3 N) ∣ 8 := by
    simpa [hindex] using Sylow.card_dvd_index P
  exact ⟨hPcard, Nat.le_of_dvd (by norm_num) hdvd⟩

private theorem m24_sylow2_perm_card_lt
    (N : Subgroup M24) (hcardN : Nat.card N = 24) :
    Nat.card (Equiv.Perm (Sylow 2 N)) < 10200960 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 N := Classical.choice (inferInstance : Nonempty (Sylow 2 N))
  have hle : Nat.card (Sylow 2 N) ≤ 3 :=
    (m24_sylow2_bounds_of_card_twenty_four N hcardN P).2
  rw [Nat.card_perm]
  calc
    (Nat.card (Sylow 2 N)).factorial ≤ Nat.factorial 3 :=
      Nat.factorial_le hle
    _ = 6 := by rfl
    _ < 10200960 := by norm_num

private theorem m24_sylow3_perm_card_lt
    (N : Subgroup M24) (hcardN : Nat.card N = 24) :
    Nat.card (Equiv.Perm (Sylow 3 N)) < 10200960 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 N := Classical.choice (inferInstance : Nonempty (Sylow 3 N))
  have hle : Nat.card (Sylow 3 N) ≤ 8 :=
    (m24_sylow3_bounds_of_card_twenty_four N hcardN P).2
  rw [Nat.card_perm]
  calc
    (Nat.card (Sylow 3 N)).factorial ≤ Nat.factorial 8 :=
      Nat.factorial_le hle
    _ = 40320 := by rfl
    _ < 10200960 := by norm_num

private theorem m24PointStabilizer_fixes_sylow2
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 2 N) (h : MulAction.stabilizer M24 (24 : Fin 24)) :
    (MulAut.conjNormal (h : M24) : MulAut N) • P = P := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M24 (24 : Fin 24)
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup H := m23EquivM24PointStabilizer.symm.isSimpleGroup
  let φ : H →* MulAut N :=
    (MulAut.conjNormal : M24 →* MulAut N).comp H.subtype
  let : MulAction H (Sylow 2 N) := MulAction.compHom _ φ
  let ρ : H →* Equiv.Perm (Sylow 2 N) :=
    MulAction.toPermHom H (Sylow 2 N)
  have hHcard : Nat.card H = 10200960 :=
    (Nat.card_congr m23EquivM24PointStabilizer.toEquiv).symm.trans m23_order
  have hρ : ρ = 1 :=
    MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ρ (by
      rw [hHcard]
      exact m24_sylow2_perm_card_lt N hcardN)
  have hh : ρ h = 1 := by rw [hρ]; rfl
  have hpoint := congrArg (fun σ : Equiv.Perm (Sylow 2 N) => σ P) hh
  change (φ h) • P = P at hpoint
  exact hpoint

private theorem m24PointStabilizer_fixes_sylow3
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 3 N) (h : MulAction.stabilizer M24 (24 : Fin 24)) :
    (MulAut.conjNormal (h : M24) : MulAut N) • P = P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M24 (24 : Fin 24)
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup H := m23EquivM24PointStabilizer.symm.isSimpleGroup
  let φ : H →* MulAut N :=
    (MulAut.conjNormal : M24 →* MulAut N).comp H.subtype
  let : MulAction H (Sylow 3 N) := MulAction.compHom _ φ
  let ρ : H →* Equiv.Perm (Sylow 3 N) :=
    MulAction.toPermHom H (Sylow 3 N)
  have hHcard : Nat.card H = 10200960 :=
    (Nat.card_congr m23EquivM24PointStabilizer.toEquiv).symm.trans m23_order
  have hρ : ρ = 1 :=
    MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ρ (by
      rw [hHcard]
      exact m24_sylow3_perm_card_lt N hcardN)
  have hh : ρ h = 1 := by rw [hρ]; rfl
  have hpoint := congrArg (fun σ : Equiv.Perm (Sylow 3 N) => σ P) hh
  change (φ h) • P = P at hpoint
  exact hpoint

private theorem m24PointStabilizer_le_normalizer_sylow2Image
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 2 N) :
    MulAction.stabilizer M24 (24 : Fin 24) ≤
      Subgroup.normalizer (P.map N.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : N.Normal := hN
  rw [Subgroup.le_normalizer_iff]
  intro h hh p hp
  rcases hp with ⟨p, hp, rfl⟩
  let hs : MulAction.stabilizer M24 (24 : Fin 24) := ⟨h, hh⟩
  have hfix := m24PointStabilizer_fixes_sylow2 N hN hcardN P hs
  have hsub := congrArg (fun R : Sylow 2 N => (R : Subgroup N)) hfix
  have hp' : (MulAut.conjNormal h : MulAut N) p ∈ (P : Subgroup N) := by
    rw [← hsub]
    exact Subgroup.smul_mem_pointwise_smul p
      (MulAut.conjNormal h) (P : Subgroup N) hp
  refine ⟨(MulAut.conjNormal h : MulAut N) p, hp', ?_⟩
  exact MulAut.conjNormal_apply h p

private theorem m24PointStabilizer_le_normalizer_sylow3Image
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 3 N) :
    MulAction.stabilizer M24 (24 : Fin 24) ≤
      Subgroup.normalizer (P.map N.subtype) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  rw [Subgroup.le_normalizer_iff]
  intro h hh p hp
  rcases hp with ⟨p, hp, rfl⟩
  let hs : MulAction.stabilizer M24 (24 : Fin 24) := ⟨h, hh⟩
  have hfix := m24PointStabilizer_fixes_sylow3 N hN hcardN P hs
  have hsub := congrArg (fun R : Sylow 3 N => (R : Subgroup N)) hfix
  have hp' : (MulAut.conjNormal h : MulAut N) p ∈ (P : Subgroup N) := by
    rw [← hsub]
    exact Subgroup.smul_mem_pointwise_smul p
      (MulAut.conjNormal h) (P : Subgroup N) hp
  refine ⟨(MulAut.conjNormal h : MulAut N) p, hp', ?_⟩
  exact MulAut.conjNormal_apply h p

private theorem mulAut_card_lt_m23_of_card_le_eight
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G ≤ 8) :
    Nat.card (MulAut G) < 10200960 := by
  have hle : Nat.card (MulAut G) ≤ Nat.card (Equiv.Perm G) :=
    Nat.card_le_card_of_injective
      (fun e : MulAut G => e.toEquiv) MulEquiv.toEquiv_injective
  rw [Nat.card_perm] at hle
  calc
    Nat.card (MulAut G) ≤ (Nat.card G).factorial := hle
    _ ≤ Nat.factorial 8 := Nat.factorial_le hcard
    _ = 40320 := by rfl
    _ < 10200960 := by norm_num

private theorem m24PointStabilizer_centralizes_sylow2Image
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 2 N) (h : MulAction.stabilizer M24 (24 : Fin 24))
    (q : P.map N.subtype) :
    (h : M24) * (q : M24) * (h : M24)⁻¹ = (q : M24) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M24 (24 : Fin 24)
  let Q : Subgroup M24 := P.map N.subtype
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup H := m23EquivM24PointStabilizer.symm.isSimpleGroup
  have hle : H ≤ Subgroup.normalizer Q :=
    m24PointStabilizer_le_normalizer_sylow2Image N hN hcardN P
  let incl : H →* Subgroup.normalizer Q := Subgroup.inclusion hle
  let ψ : H →* MulAut Q := Q.normalizerMonoidHom.comp incl
  have hPcard : Nat.card P = 8 :=
    (m24_sylow2_bounds_of_card_twenty_four N hcardN P).1
  have hQcard : Nat.card Q = 8 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hPcard
  have hHcard : Nat.card H = 10200960 :=
    (Nat.card_congr m23EquivM24PointStabilizer.toEquiv).symm.trans m23_order
  have hψ : ψ = 1 :=
    MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ψ (by
      rw [hHcard]
      exact mulAut_card_lt_m23_of_card_le_eight (by rw [hQcard]))
  have hψh : ψ h = 1 := by rw [hψ]; rfl
  have happly := congrArg (fun e : MulAut Q => e q) hψh
  have hval := congrArg (fun z : Q => (z : M24)) happly
  change (h : M24) * (q : M24) * (h : M24)⁻¹ = (q : M24) at hval
  exact hval

private theorem m24PointStabilizer_centralizes_sylow3Image
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (P : Sylow 3 N) (h : MulAction.stabilizer M24 (24 : Fin 24))
    (q : P.map N.subtype) :
    (h : M24) * (q : M24) * (h : M24)⁻¹ = (q : M24) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M24 (24 : Fin 24)
  let Q : Subgroup M24 := P.map N.subtype
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup H := m23EquivM24PointStabilizer.symm.isSimpleGroup
  have hle : H ≤ Subgroup.normalizer Q :=
    m24PointStabilizer_le_normalizer_sylow3Image N hN hcardN P
  let incl : H →* Subgroup.normalizer Q := Subgroup.inclusion hle
  let ψ : H →* MulAut Q := Q.normalizerMonoidHom.comp incl
  have hPcard : Nat.card P = 3 :=
    (m24_sylow3_bounds_of_card_twenty_four N hcardN P).1
  have hQcard : Nat.card Q = 3 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hPcard
  have hHcard : Nat.card H = 10200960 :=
    (Nat.card_congr m23EquivM24PointStabilizer.toEquiv).symm.trans m23_order
  have hψ : ψ = 1 :=
    MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ψ (by
      rw [hHcard]
      exact mulAut_card_lt_m23_of_card_le_eight (by rw [hQcard]; norm_num))
  have hψh : ψ h = 1 := by rw [hψ]; rfl
  have happly := congrArg (fun e : MulAut Q => e q) hψh
  have hval := congrArg (fun z : Q => (z : M24)) happly
  change (h : M24) * (q : M24) * (h : M24)⁻¹ = (q : M24) at hval
  exact hval

private theorem m24PointStabilizer_commutes_regularNormal
    (N : Subgroup M24) (hN : N.Normal) (hcardN : Nat.card N = 24)
    (h : MulAction.stabilizer M24 (24 : Fin 24)) (n : N) :
    (h : M24) * (n : M24) = (n : M24) * (h : M24) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P2 : Sylow 2 N := Classical.choice (inferInstance : Nonempty (Sylow 2 N))
  let P3 : Sylow 3 N := Classical.choice (inferInstance : Nonempty (Sylow 3 N))
  let Q2 : Subgroup M24 := P2.map N.subtype
  let Q3 : Subgroup M24 := P3.map N.subtype
  let R : Subgroup M24 := Q2 ⊔ Q3
  have hP2card : Nat.card P2 = 8 :=
    (m24_sylow2_bounds_of_card_twenty_four N hcardN P2).1
  have hP3card : Nat.card P3 = 3 :=
    (m24_sylow3_bounds_of_card_twenty_four N hcardN P3).1
  have hQ2card : Nat.card Q2 = 8 := by
    dsimp [Q2]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hP2card
  have hQ3card : Nat.card Q3 = 3 := by
    dsimp [Q3]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hP3card
  have hQ2leN : Q2 ≤ N := by
    dsimp [Q2]
    exact Subgroup.map_subtype_le (P2 : Subgroup N)
  have hQ3leN : Q3 ≤ N := by
    dsimp [Q3]
    exact Subgroup.map_subtype_le (P3 : Subgroup N)
  have hRleN : R ≤ N := sup_le hQ2leN hQ3leN
  have h8dvd : 8 ∣ Nat.card R := by
    rw [← hQ2card]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h3dvd : 3 ∣ Nat.card R := by
    rw [← hQ3card]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h24dvd : 24 ∣ Nat.card R := by
    exact (by norm_num : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd h8dvd h3dvd
  have hRcardLe : Nat.card R ≤ 24 := by
    calc
      Nat.card R ≤ Nat.card N := Subgroup.card_le_of_le hRleN
      _ = 24 := hcardN
  have hRcardGe : 24 ≤ Nat.card R :=
    Nat.le_of_dvd (Nat.card_pos) h24dvd
  have hRcard : Nat.card R = 24 := Nat.le_antisymm hRcardLe hRcardGe
  have hReqN : R = N := by
    apply Subgroup.eq_of_le_of_card_ge hRleN
    omega
  let C : Subgroup M24 := Subgroup.centralizer ({(h : M24)} : Set M24)
  have hQ2leC : Q2 ≤ C := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let q' : P2.map N.subtype := ⟨q, hq⟩
    have hcentral :=
      m24PointStabilizer_centralizes_sylow2Image N hN hcardN P2 h q'
    calc
      (h : M24) * q =
          ((h : M24) * q * (h : M24)⁻¹) * (h : M24) := by
            simp [mul_assoc]
      _ = q * (h : M24) := by rw [hcentral]
  have hQ3leC : Q3 ≤ C := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let q' : P3.map N.subtype := ⟨q, hq⟩
    have hcentral :=
      m24PointStabilizer_centralizes_sylow3Image N hN hcardN P3 h q'
    calc
      (h : M24) * q =
          ((h : M24) * q * (h : M24)⁻¹) * (h : M24) := by
            simp [mul_assoc]
      _ = q * (h : M24) := by rw [hcentral]
  have hRleC : R ≤ C := sup_le hQ2leC hQ3leC
  have hnR : (n : M24) ∈ R := by
    rw [hReqN]
    exact n.property
  have hnC : (n : M24) ∈ C := hRleC hnR
  exact (Subgroup.mem_centralizer_iff.mp hnC)
    (h : M24) (Set.mem_singleton (h : M24))

/-- A transitive normal subgroup of M24 with trivial point stabilizer cannot have order 24. -/
public theorem m24_no_regular_normal
    (N : Subgroup M24) (hN : N.Normal)
    [MulAction.IsPretransitive N (Fin 24)]
    (hcardN : Nat.card N = 24) : False := by
  classical
  let H := MulAction.stabilizer M24 (24 : Fin 24)
  have hHcard : Nat.card H = 10200960 :=
    (Nat.card_congr m23EquivM24PointStabilizer.toEquiv).symm.trans m23_order
  have hHidentity (h : H) : h = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨n, hn⟩ :=
      MulAction.exists_smul_eq N (24 : Fin 24) x
    have hn' : (n : M24) • (24 : Fin 24) = x := hn
    have hcomm :=
      m24PointStabilizer_commutes_regularNormal N hN hcardN h n
    change (h : M24) • x = x
    calc
      (h : M24) • x =
          (h : M24) • ((n : M24) • (24 : Fin 24)) := by rw [hn']
      _ = ((h : M24) * (n : M24)) • (24 : Fin 24) := by
        rw [mul_smul]
      _ = ((n : M24) * (h : M24)) • (24 : Fin 24) := by rw [hcomm]
      _ = (n : M24) • ((h : M24) • (24 : Fin 24)) := by
        rw [mul_smul]
      _ = (n : M24) • (24 : Fin 24) := by rw [h.property]
      _ = x := hn'
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hHcard]
    norm_num)
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  exact hh (hHidentity h)

open MulAction

private theorem m24_normalIntersection_eq_bot_or_eq_top
    (N : Subgroup M24) (hN : N.Normal) :
    N.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype = ⊥ ∨
      N.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype = ⊤ := by
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  let : IsSimpleGroup (MulAction.stabilizer M24 (24 : Fin 24)) :=
    m23EquivM24PointStabilizer.symm.isSimpleGroup
  let : N.Normal := hN
  let :
      (N.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype).Normal :=
    hN.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype
  exact
    (inferInstance :
      (N.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype).Normal).eq_bot_or_eq_top

/-- The Mathieu group M24 is simple. -/
public theorem m24_isSimpleGroup : IsSimpleGroup M24 := by
  classical
  let : MulAction.IsPreprimitive M24 (Fin 24) := m24_isPreprimitive
  let : Nontrivial M24 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [m24_order]
    norm_num)
  apply IsSimpleGroup.mk
  intro N hN
  let : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  have hfix : MulAction.fixedPoints N (Fin 24) ≠ Set.univ := by
    intro h
    apply hNbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.fixedPoints N (Fin 24) := by
      rw [h]
      exact Set.mem_univ x
    have hxn := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
    change (n : Equiv.Perm (Fin 24)) x = x at hxn
    exact hxn
  let : MulAction.IsPretransitive N (Fin 24) :=
    (inferInstance :
      MulAction.IsQuasiPreprimitive M24 (Fin 24)).isPretransitive_of_normal hfix
  rcases m24_normalIntersection_eq_bot_or_eq_top N hN with hKbot | hKtop
  · have hcardN : Nat.card N = 24 := by
      simpa using
        (MulAction.card_eq_card_of_comap_stabilizer_eq_bot N (24 : Fin 24) hKbot)
    exfalso
    exact m24_no_regular_normal N hN hcardN
  · have hHle : MulAction.stabilizer M24 (24 : Fin 24) ≤ N := by
      intro g hg
      let h : MulAction.stabilizer M24 (24 : Fin 24) := ⟨g, hg⟩
      have hh :
          h ∈ N.comap (MulAction.stabilizer M24 (24 : Fin 24)).subtype := by
        rw [hKtop]
        exact Subgroup.mem_top h
      exact hh
    exact MulAction.eq_top_of_stabilizer_le N (24 : Fin 24) hHle

end Sporadic.Mathieu
