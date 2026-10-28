module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.Mathieu.M11.Properties.Simplicity
public import Theory.Mathieu.M12.Properties.PointStabilizer
public import Theory.Mathieu.M12.Properties.Order
public import Theory.GroupTheory.Simple
public import Theory.GroupAction.Stabilizer

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
open MulAction
open scoped Pointwise

private theorem m12PointStabilizer_isPretransitive :
    IsPretransitive (MulAction.stabilizer M12 (12 : Fin 12))
      (SubMulAction.ofStabilizer M12 (12 : Fin 12)) := by
  constructor
  intro x y
  obtain ⟨i, hi⟩ := m11M12PointEquiv.surjective x
  obtain ⟨j, hj⟩ := m11M12PointEquiv.surjective y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M11 i j
  refine ⟨m11ToM12PointStabilizer g, ?_⟩
  apply Subtype.ext
  change ((m11ToM12PointStabilizer g : M12) : Equiv.Perm (Fin 12)) x.1 = y.1
  rw [← hi, ← hj]
  simp only [m11ToM12PointStabilizer, MonoidHom.codRestrict_apply]
  change m11ToM12ExtendHom g (m11M12PointEmbedding i) =
    m11M12PointEmbedding j
  rw [m11ToM12ExtendHom_apply_embedded]
  exact congrArg m11M12PointEmbedding hg






private theorem sylow3_bounds_of_card_twelve (N : Subgroup M12) (hcardN : Nat.card N = 12)
    (P : Sylow 3 N) : Nat.card P = 3 ∧ Nat.card (Sylow 3 N) ≤ 4 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : Nat.factorization 12 3 = 1 := by
    have hzero : padicValNat 3 4 = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hle : 1 ≤ padicValNat 3 4 := hpos
      have hdvd : 3 ^ 1 ∣ 4 :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) (by norm_num)).mpr hle
      norm_num at hdvd
    rw [Nat.factorization_def _ Nat.prime_three,
      show (12 : ℕ) = 3 * 4 by norm_num,
      padicValNat_base_mul (by norm_num) (by norm_num), hzero]
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hcardN, hfac]
    norm_num
  have hmul := Subgroup.card_mul_index (P : Subgroup N)
  rw [hPcard, hcardN] at hmul
  have hindex : P.index = 4 := by omega
  have hdvd : Nat.card (Sylow 3 N) ∣ 4 := by
    simpa [hindex] using Sylow.card_dvd_index P
  exact ⟨hPcard, Nat.le_of_dvd (by norm_num) hdvd⟩

private theorem sylow3_perm_card_lt_of_card_twelve (N : Subgroup M12) (hcardN : Nat.card N = 12) :
    Nat.card (Equiv.Perm (Sylow 3 N)) < 7920 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 N := Classical.choice (inferInstance : Nonempty (Sylow 3 N))
  have hle : Nat.card (Sylow 3 N) ≤ 4 := (sylow3_bounds_of_card_twelve N hcardN P).2
  rw [Nat.card_perm]
  calc
    (Nat.card (Sylow 3 N)).factorial ≤ Nat.factorial 4 := Nat.factorial_le hle
    _ = 24 := by rfl
    _ < 7920 := by norm_num

private theorem m12PointStabilizer_fixes_sylow3
    (N : Subgroup M12) (hN : N.Normal) (hcardN : Nat.card N = 12)
    (P : Sylow 3 N) (h : MulAction.stabilizer M12 (12 : Fin 12)) :
    (MulAut.conjNormal (h : M12) : MulAut N) • P = P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M12 (12 : Fin 12)
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  let : IsSimpleGroup H := m11EquivM12PointStabilizer.symm.isSimpleGroup
  let φ : H →* MulAut N :=
    (MulAut.conjNormal : M12 →* MulAut N).comp H.subtype
  let : MulAction H (Sylow 3 N) := MulAction.compHom _ φ
  let ρ : H →* Equiv.Perm (Sylow 3 N) := MulAction.toPermHom H (Sylow 3 N)
  have hHcard : Nat.card H = 7920 :=
    (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).symm.trans m11_order
  have hρ : ρ = 1 := MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ρ (by
    rw [hHcard]
    exact sylow3_perm_card_lt_of_card_twelve N hcardN)
  have hh : ρ h = 1 := by rw [hρ]; rfl
  have hpoint := congrArg (fun σ : Equiv.Perm (Sylow 3 N) => σ P) hh
  change (φ h) • P = P at hpoint
  change (φ h) • P = P
  exact hpoint

private theorem m12PointStabilizer_le_normalizer_sylow3Image
    (N : Subgroup M12) (hN : N.Normal) (hcardN : Nat.card N = 12)
    (P : Sylow 3 N) :
    MulAction.stabilizer M12 (12 : Fin 12) ≤ Subgroup.normalizer (P.map N.subtype) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  rw [Subgroup.le_normalizer_iff]
  intro h hh p hp
  rcases hp with ⟨p, hp, rfl⟩
  let hs : MulAction.stabilizer M12 (12 : Fin 12) := ⟨h, hh⟩
  have hfix := m12PointStabilizer_fixes_sylow3 N hN hcardN P hs
  have hsub := congrArg (fun R : Sylow 3 N => (R : Subgroup N)) hfix
  have hp' : (MulAut.conjNormal h : MulAut N) p ∈ (P : Subgroup N) := by
    rw [← hsub]
    exact Subgroup.smul_mem_pointwise_smul p (MulAut.conjNormal h) (P : Subgroup N) hp
  refine ⟨(MulAut.conjNormal h : MulAut N) p, hp', ?_⟩
  exact MulAut.conjNormal_apply h p

private theorem mulAut_card_lt_of_card_three
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 3) :
    Nat.card (MulAut G) < 7920 := by
  have hle : Nat.card (MulAut G) ≤ Nat.card (Equiv.Perm G) :=
    Nat.card_le_card_of_injective (fun e : MulAut G => e.toEquiv)
      MulEquiv.toEquiv_injective
  rw [Nat.card_perm, hcard] at hle
  calc
    Nat.card (MulAut G) ≤ Nat.factorial 3 := hle
    _ = 6 := by rfl
    _ < 7920 := by norm_num

private theorem m12PointStabilizer_centralizes_sylow3Image
    (N : Subgroup M12) (hN : N.Normal) (hcardN : Nat.card N = 12)
    (P : Sylow 3 N) (h : MulAction.stabilizer M12 (12 : Fin 12))
    (q : P.map N.subtype) : (h : M12) * (q : M12) * (h : M12)⁻¹ = (q : M12) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M12 (12 : Fin 12)
  let Q : Subgroup M12 := P.map N.subtype
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  let : IsSimpleGroup H := m11EquivM12PointStabilizer.symm.isSimpleGroup
  have hle : H ≤ Subgroup.normalizer Q :=
    m12PointStabilizer_le_normalizer_sylow3Image N hN hcardN P
  let incl : H →* Subgroup.normalizer Q := Subgroup.inclusion hle
  let ψ : H →* MulAut Q := Q.normalizerMonoidHom.comp incl
  have hPcard : Nat.card P = 3 := (sylow3_bounds_of_card_twelve N hcardN P).1
  have hQcard : Nat.card Q = 3 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hPcard
  have hψ : ψ = 1 := MonoidHom.eq_one_of_isSimpleGroup_of_card_lt ψ (by
    have hHcard : Nat.card H = 7920 :=
      (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).symm.trans m11_order
    rw [hHcard]
    exact mulAut_card_lt_of_card_three hQcard)
  have hψh : ψ h = 1 := by rw [hψ]; rfl
  have happly := congrArg (fun e : MulAut Q => e q) hψh
  have hval := congrArg (fun z : Q => (z : M12)) happly
  change (h : M12) * (q : M12) * (h : M12)⁻¹ = (q : M12) at hval
  exact hval

private theorem no_regular_normal_of_card_twelve
    (N : Subgroup M12) (hN : N.Normal)
    [MulAction.IsPretransitive N (Fin 12)]
    (hK : N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype = ⊥)
    (hcardN : Nat.card N = 12) : False := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : N.Normal := hN
  let P : Sylow 3 N := Classical.choice (inferInstance : Nonempty (Sylow 3 N))
  let Q : Subgroup M12 := P.map N.subtype
  have hPcard : Nat.card P = 3 := (sylow3_bounds_of_card_twelve N hcardN P).1
  have hQcard : Nat.card Q = 3 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hPcard
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQcard]; norm_num)
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  let qN : N := ⟨(q : M12), (Subgroup.map_subtype_le P) q.property⟩
  have hStab : MulAction.stabilizer N (12 : Fin 12) = ⊥ :=
    MulAction.stabilizer_eq_bot_of_comap_eq_bot N (12 : Fin 12) hK
  have hqmove : (q : M12) • (12 : Fin 12) ≠ (12 : Fin 12) := by
    intro hfix
    have hmem : qN ∈ MulAction.stabilizer N (12 : Fin 12) := hfix
    rw [hStab] at hmem
    have hqN1 : qN = 1 := Subgroup.mem_bot.mp hmem
    apply hq
    apply Subtype.ext
    exact congrArg (fun z : N => (z : M12)) hqN1
  let X := SubMulAction.ofStabilizer M12 (12 : Fin 12)
  let y : X := ⟨(q : M12) • (12 : Fin 12), hqmove⟩
  let : MulAction.IsPretransitive (MulAction.stabilizer M12 (12 : Fin 12)) X :=
    m12PointStabilizer_isPretransitive
  let : Nontrivial X := ⟨⟨⟨(1 : Fin 12), by
    intro h
    have hval := congrArg Fin.val h
    norm_num at hval⟩, ⟨(2 : Fin 12), by
    intro h
    have hval := congrArg Fin.val h
    norm_num at hval⟩, by
    intro h
    have hval : (1 : Fin 12) = 2 := congrArg Subtype.val h
    have hnat := congrArg Fin.val hval
    norm_num at hnat⟩⟩
  obtain ⟨z, hyz⟩ := exists_ne y
  obtain ⟨h, hhy⟩ := MulAction.exists_smul_eq
    (MulAction.stabilizer M12 (12 : Fin 12)) y z
  have hcentral := m12PointStabilizer_centralizes_sylow3Image N hN hcardN P h q
  have hcomm : (h : M12) * (q : M12) = (q : M12) * (h : M12) := by
    calc
      (h : M12) * (q : M12) =
          ((h : M12) * (q : M12) * (h : M12)⁻¹) * (h : M12) := by simp [mul_assoc]
      _ = (q : M12) * (h : M12) := by rw [hcentral]
  have hfixy : h • y = y := by
    apply Subtype.ext
    change ((h : M12) * (q : M12)) • (12 : Fin 12) =
      (q : M12) • (12 : Fin 12)
    rw [hcomm, mul_smul, h.property]
  exact hyz (hhy.symm.trans hfixy)
private theorem normalIntersection_eq_bot_or_eq_top (N : Subgroup M12) (hN : N.Normal) :
    N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype = ⊥ ∨
      N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype = ⊤ := by
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  let : IsSimpleGroup (MulAction.stabilizer M12 (12 : Fin 12)) :=
    m11EquivM12PointStabilizer.symm.isSimpleGroup
  let : N.Normal := hN
  let : (N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype).Normal :=
    hN.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype
  exact (inferInstance : (N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype).Normal).eq_bot_or_eq_top
private theorem m12_isTwoPretransitive :
    IsMultiplyPretransitive M12 (Fin 12) 2 := by
  have : IsPretransitive (MulAction.stabilizer M12 (12 : Fin 12))
      (SubMulAction.ofStabilizer M12 (12 : Fin 12)) := m12PointStabilizer_isPretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M12) (α := Fin 12) (a := (12 : Fin 12)) (n := 1)).2
  exact MulAction.is_one_pretransitive_iff.mpr inferInstance

private theorem m12_isPreprimitive : IsPreprimitive M12 (Fin 12) :=
  MulAction.isPreprimitive_of_is_two_pretransitive m12_isTwoPretransitive

/-- The Mathieu group M12 is simple. -/
public theorem m12_isSimpleGroup : IsSimpleGroup M12 := by
  classical
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  let : MulAction.IsPreprimitive M12 (Fin 12) := m12_isPreprimitive
  let : Nontrivial M12 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [m12_order]
    norm_num)
  apply IsSimpleGroup.mk
  intro N hN
  let : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  have hfix : MulAction.fixedPoints N (Fin 12) ≠ Set.univ := by
    intro h
    apply hNbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.fixedPoints N (Fin 12) := by
      rw [h]
      exact Set.mem_univ x
    have hxn := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
    change (n : Equiv.Perm (Fin 12)) x = x at hxn
    exact hxn
  let : MulAction.IsPretransitive N (Fin 12) :=
    (inferInstance : MulAction.IsQuasiPreprimitive M12 (Fin 12)).isPretransitive_of_normal hfix
  rcases normalIntersection_eq_bot_or_eq_top N hN with hKbot | hKtop
  · have hcardN : Nat.card N = 12 := by
      simpa using
        (MulAction.card_eq_card_of_comap_stabilizer_eq_bot N (12 : Fin 12) hKbot)
    exfalso
    exact no_regular_normal_of_card_twelve N hN hKbot hcardN
  · have hHle : MulAction.stabilizer M12 (12 : Fin 12) ≤ N := by
      intro g hg
      let h : MulAction.stabilizer M12 (12 : Fin 12) := ⟨g, hg⟩
      have hh : h ∈ N.comap (MulAction.stabilizer M12 (12 : Fin 12)).subtype := by
        rw [hKtop]
        exact Subgroup.mem_top h
      exact hh
    exact MulAction.eq_top_of_stabilizer_le N (12 : Fin 12) hHle

end Sporadic.Mathieu
