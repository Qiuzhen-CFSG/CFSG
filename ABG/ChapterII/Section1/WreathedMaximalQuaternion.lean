module
public import ABG.ChapterII.Section1.WreathedNormalForm
public import ABG.ChapterII.Section1.WreathedRelations
public import Theory.GroupTheory.QuaternionGenerated
public import ABG.ChapterII.Section1.NormalForm

/-!
# The normal quaternion subgroup of a wreathed group

For a chosen wreathed presentation of height n ≥ 2, the subgroup Y generated
by r = st⁻¹ and d = x₂z is generalized quaternion of order 2^(n+1) and normal.
This is the existence and normality part of Alperin–Brauer–Gorenstein,
Chapter II §1 Lemma 2(v), article p.9. Uniqueness is assembled separately.

Unique coordinates give r exact order 2^n and place d outside its cyclic
subgroup. The relations d² = r^(2^(n-1)) and d*r*d⁻¹ = r⁻¹ yield two cosets
of that cyclic subgroup in Y. Their cardinality permits the existing
generic quaternion closure recognizer in `QuaternionGenerated` to identify Y with QuaternionGroup
(2^(n-1)). For normality, conjugation by each of s,t,z sends r and d into Y;
finiteness turns these inclusions into equality under conjugation. The
ambient generation relation then gives normality in the whole group.
The conjugation formula for d is public for the subsequent normal-closure result.
-/

namespace ABG.Wreathed
variable {G : Type*} [Group G]

private theorem normalizer_of_conjugate_generators {c d : G}
    [Finite (Subgroup.closure ({c,d} : Set G))] (g : G)
    (hc : g * c * g⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (hd : g * d * g⁻¹ ∈ Subgroup.closure ({c,d} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({c,d} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, hx, rfl⟩
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hc
    · exact Set.mem_singleton_iff.mp hx ▸ hd
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem normal_of_generator_conjugates (s t z c d : G)
    (hgen : Subgroup.closure ({s,t,z} : Set G) = ⊤)
    [Finite (Subgroup.closure ({c,d} : Set G))]
    (hsc : s * c * s⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (hsd : s * d * s⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (htc : t * c * t⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (htd : t * d * t⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (hzc : z * c * z⁻¹ ∈ Subgroup.closure ({c,d} : Set G))
    (hzd : z * d * z⁻¹ ∈ Subgroup.closure ({c,d} : Set G)) :
    (Subgroup.closure ({c,d} : Set G)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact normalizer_of_conjugate_generators _ hsc hsd
  · exact normalizer_of_conjugate_generators _ htc htd
  · exact normalizer_of_conjugate_generators _ hzc hzd

end ABG.Wreathed
namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem normal_relations :
    P.s * P.r * P.s⁻¹ = P.r ∧ P.t * P.r * P.t⁻¹ = P.r ∧
    P.s * P.d * P.s⁻¹ = P.r * P.d ∧
    P.t * P.d * P.t⁻¹ = P.r⁻¹ * P.d ∧
    P.z * P.d * P.z⁻¹ = P.r⁻¹ ^ (2 ^ (n - 1)) * P.d := by
  have hst : Commute P.s P.t := P.commute
  have hz : P.z⁻¹ = P.z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using P.z_sq)
  have hzs : P.z * P.s * P.z⁻¹ = P.t := by simpa [hz] using P.conj_s
  have hzt : P.z * P.t * P.z⁻¹ = P.s := by simpa [hz] using P.conj_t
  have hzs' : P.z * P.s⁻¹ = P.t⁻¹ * P.z := by
    have h := congrArg Inv.inv hzs
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at h
    calc
      _ = (P.z * P.s⁻¹ * P.z⁻¹) * P.z := by group
      _ = _ := by rw [h]
  have hzt' : P.z * P.t⁻¹ = P.s⁻¹ * P.z := by
    have h := congrArg Inv.inv hzt
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at h
    calc
      _ = (P.z * P.t⁻¹ * P.z⁻¹) * P.z := by group
      _ = _ := by rw [h]
  have hsx : Commute P.s P.x₂ := Commute.self_pow _ _
  have htx : Commute P.t P.x₂ := hst.symm.pow_right _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hsr : Commute P.s P.r := (Commute.refl P.s).mul_right hst.inv_right
    rw [hsr.eq]; group
  · dsimp [r]
    rw [← mul_assoc P.t, hst.symm.eq]
    group
  · dsimp [d, r]
    calc
      _ = P.s * P.x₂ * (P.z * P.s⁻¹) := by group
      _ = P.s * P.x₂ * (P.t⁻¹ * P.z) := by rw [hzs']
      _ = _ := by rw [mul_assoc, ← mul_assoc P.x₂, htx.symm.inv_right.eq]; group
  · dsimp [d, r]
    calc
      _ = P.t * P.x₂ * (P.z * P.t⁻¹) := by group
      _ = P.t * P.x₂ * (P.s⁻¹ * P.z) := by rw [hzt']
      _ = _ := by rw [mul_assoc, ← mul_assoc P.x₂, hsx.symm.inv_right.eq]; group
  · have hzx : P.z * P.x₂ * P.z⁻¹ = P.t ^ (2 ^ (n - 1)) := by
      change (MulAut.conj P.z) (P.s ^ _) = _
      rw [map_pow]
      exact congrArg (· ^ (2 ^ (n - 1))) hzs
    dsimp [d]
    calc
      _ = (P.z * P.x₂ * P.z⁻¹) * P.z := by group
      _ = P.t ^ (2 ^ (n - 1)) * P.z := by rw [hzx]
      _ = _ := by
        simp only [r, mul_inv_rev, inv_inv, hst.symm.inv_right.mul_pow]
        dsimp [x₂]
        group

end ABG.Wreathed.Presentation
namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- The difference generator has the full cyclic order prescribed by the presentation. -/
public theorem r_order : orderOf P.r = 2 ^ n := by
  have hpow (k : ℕ) : P.r ^ k = P.s ^ (k : ℤ) * P.t ^ (-(k : ℤ)) := by
    simp only [r, (show Commute P.s P.t from P.commute).inv_right.mul_pow,
      zpow_neg, zpow_natCast, inv_pow]
  apply (orderOf_eq_iff (by positivity)).mpr
  constructor
  · rw [hpow]
    simp only [zpow_neg, zpow_natCast, P.s_pow, P.t_pow, inv_one, mul_one]
  · intro k hkn hk h
    have he := (P.normal_form_zpow_eq_iff k (-(k : ℤ)) 0 0 0 0).mp (by
      simpa only [zpow_zero, mul_one, one_mul, ← hpow] using h)
    have he' : (k : ℤ) % (2 ^ n : ℕ) = 0 := by simpa using he.1
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hkn)] at he'
    omega

/-- The quaternion generator lies outside the cyclic subgroup generated by r. -/
public theorem d_not_mem_zpowers_r : P.d ∉ Subgroup.zpowers P.r := by
  rintro ⟨i, hi⟩
  have hpow : P.r ^ i = P.s ^ i * P.t ^ (-i) := by
    simp only [r, (show Commute P.s P.t from P.commute).inv_right.mul_zpow,
      inv_zpow, zpow_neg]
  have he := (P.normal_form_zpow_eq_iff i (-i) 0 ((2 ^ (n - 1) : ℕ) : ℤ) 0 1).mp (by
    simpa only [d, x₂, zpow_zero, zpow_one, mul_one, zpow_natCast, ← hpow] using hi)
  norm_num at he

/-- ABG II.1.2(v): the designated subgroup is normal generalized quaternion of order 2^(n+1). -/
public theorem quaternion_subgroup :
    ABG.IsGeneralizedQuaternionGroup P.Y ∧ Nat.card P.Y = 2 ^ (n + 1) ∧ P.Y.Normal := by
  have hn := P.height
  have he : 2 * 2 ^ (n - 1) = 2 ^ n := by
    conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hc : orderOf P.r = 2 * 2 ^ (n - 1) := by rw [P.r_order, he]
  obtain ⟨hcard, hmodel⟩ := QuaternionGroup.closure_equiv_of_relations (by positivity) P.r P.d hc
    P.d_sq P.d_conj_r P.d_not_mem_zpowers_r
  have hcard' : Nat.card P.Y = 2 ^ (n + 1) := by
    change Nat.card (Subgroup.closure ({P.r,P.d} : Set S)) = _
    rw [hcard, pow_succ, ← he]
    ring
  refine ⟨⟨n - 1, by omega, hmodel⟩, hcard', ?_⟩
  let : Finite (Subgroup.closure ({P.r,P.d} : Set S)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hr : P.r ∈ P.Y := Subgroup.subset_closure (by simp)
  have hd : P.d ∈ P.Y := Subgroup.subset_closure (by simp)
  obtain ⟨hsr, htr, hsd, htd, hzd⟩ := P.normal_relations
  exact normal_of_generator_conjugates P.s P.t P.z P.r P.d P.generate
    (by rw [hsr]; exact hr) (by rw [hsd]; exact P.Y.mul_mem hr hd)
    (by rw [htr]; exact hr) (by rw [htd]; exact P.Y.mul_mem (P.Y.inv_mem hr) hd)
    (by rw [P.z_conj_r]; exact P.Y.inv_mem hr)
    (by rw [hzd]; exact P.Y.mul_mem (P.Y.pow_mem (P.Y.inv_mem hr) _) hd)

/-- Conjugating d by s introduces the cyclic generator r. -/
public theorem s_conj_d : P.s * P.d * P.s⁻¹ = P.r * P.d :=
  P.normal_relations.2.2.1

end ABG.Wreathed.Presentation
