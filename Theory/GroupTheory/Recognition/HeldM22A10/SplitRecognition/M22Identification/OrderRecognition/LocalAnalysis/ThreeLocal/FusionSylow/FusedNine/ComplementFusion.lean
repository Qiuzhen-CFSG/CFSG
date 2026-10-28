module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary

/-!
# Order-three fusion in the two elementary normalizers

A subgroup of index prime to three contains a conjugate of every element
of order three. Apply this to the actual complements of E and F. Three-cycles
in S₅ commute with involutions, while A₆ has at most two classes of elements
of order three. All conjugators are transported through the supplied group
equivalences and the actual normalizer inclusions.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed pp.7–8.
-/

open Subgroup Equiv Equiv.Perm
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy

private def r₁ : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide +kernel⟩
private def r₂ : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5), by rw [mem_alternatingGroup]; decide +kernel⟩

private theorem alternating_conj_of_odd_centralizer
    {x y : alternatingGroup (Fin 6)} (s : Perm (Fin 6))
    (hs : sign s = -1) (hc : s * (x : Perm (Fin 6)) * s⁻¹ = x)
    (hxy : IsConj (x : Perm (Fin 6)) (y : Perm (Fin 6))) : IsConj x y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  by_cases hpe : p ∈ alternatingGroup (Fin 6)
  · exact isConj_iff.mpr ⟨⟨p, hpe⟩, Subtype.ext hp⟩
  · have hps : sign p = -1 := by
      rcases Int.units_eq_one_or (sign p) with h | h
      · exact (hpe (mem_alternatingGroup.mpr h)).elim
      · exact h
    have hqe : p * s ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup, map_mul, hps, hs]
      norm_num
    apply isConj_iff.mpr
    refine ⟨⟨p * s, hqe⟩, Subtype.ext ?_⟩
    change (p * s) * (x : Perm (Fin 6)) * (p * s)⁻¹ = (y : Perm (Fin 6))
    calc
      _ = p * (s * (x : Perm (Fin 6)) * s⁻¹) * p⁻¹ := by group
      _ = (y : Perm (Fin 6)) := by rw [hc, hp]

private theorem alternating_six_three_classes
    (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) : IsConj r₁ x ∨ IsConj r₂ x := by
  have h : ∀ x : alternatingGroup (Fin 6), x ^ 3 = 1 → x ≠ 1 →
      (x : Perm (Fin 6)).cycleType = {3} ∨ (x : Perm (Fin 6)).cycleType = {3, 3} := by
    decide +kernel
  rcases h x (by rw [← hx]; exact pow_orderOf_eq_one x)
    (by intro he; simp [he] at hx) with h | h
  · left
    apply alternating_conj_of_odd_centralizer (swap 3 4) (by decide +kernel) (by decide +kernel)
    apply isConj_iff_cycleType_eq.mpr
    exact (show (r₁ : Perm (Fin 6)).cycleType = {3} from by decide +kernel).trans h.symm
  · right
    apply alternating_conj_of_odd_centralizer (swap 0 3 * swap 1 4 * swap 2 5)
      (by decide +kernel) (by decide +kernel)
    apply isConj_iff_cycleType_eq.mpr
    exact (show (r₂ : Perm (Fin 6)).cycleType = {3, 3} from by decide +kernel).trans h.symm

private theorem alternating_six_three_trichotomy (x y z : alternatingGroup (Fin 6))
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hz : orderOf z = 3) :
    IsConj x y ∨ IsConj x z ∨ IsConj y z := by
  rcases alternating_six_three_classes x hx with h₁ | h₁ <;>
    rcases alternating_six_three_classes y hy with h₂ | h₂ <;>
    rcases alternating_six_three_classes z hz with h₃ | h₃
  all_goals first | exact Or.inl (h₁.symm.trans h₂) |
    exact Or.inr (Or.inl (h₁.symm.trans h₃)) | exact Or.inr (Or.inr (h₂.symm.trans h₃))

private theorem prime_element_conjugate_into
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (K : Subgroup A) (hK : ¬p ∣ K.index) (x : A) (hx : orderOf x = p) :
    ∃ y : K, IsConj x (y : A) := by
  let T : Sylow p K := Classical.choice inferInstance
  let R := (T : Subgroup K).map K.subtype
  have hi : ¬p ∣ R.index := by
    rw [index_map_subtype]
    exact (Fact.out : Nat.Prime p).not_dvd_mul T.not_dvd_index hK
  let T' : Sylow p A := (T.isPGroup'.map K.subtype).toSylow hi
  have hQ : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S T'
  have hm : (MulAut.conj g) x ∈ R := by
    change (MulAut.conj g) x ∈ (T' : Subgroup A)
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul x (MulAut.conj g) (S : Subgroup A) (hS (mem_zpowers x))
  obtain ⟨y, _, hy⟩ := hm
  exact ⟨y, isConj_iff.mpr ⟨g, hy.symm⟩⟩

private theorem symmetric_five_three_commutes_involution
    (x : Equiv.Perm (Fin 5)) (hx : orderOf x = 3) :
    ∃ t : Equiv.Perm (Fin 5), orderOf t = 2 ∧ Commute x t := by
  have h : ∀ x : Equiv.Perm (Fin 5), x ^ 3 = 1 → x ≠ 1 →
      ∃ t : Equiv.Perm (Fin 5), t ^ 2 = 1 ∧ t ≠ 1 ∧ x * t = t * x := by
    decide +kernel
  obtain ⟨t, ht, ht1, hxt⟩ := h x (by rw [← hx]; exact pow_orderOf_eq_one x)
    (by intro h; simp [h] at hx)
  exact ⟨t, orderOf_eq_prime ht ht1, hxt⟩

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

public theorem three_in_normalizer_F_commutes_involution
    (hF : ∃ K : Subgroup (normalizer (CaseII.F D k : Set G)),
      ((CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G))).IsComplement' K ∧
        Nonempty (K ≃* Equiv.Perm (Fin 5)))
    (x : G) (hxF : x ∈ normalizer (CaseII.F D k : Set G)) (hx : orderOf x = 3) :
    ∃ t : G, orderOf t = 2 ∧ Commute x t := by
  let N := normalizer (CaseII.F D k : Set G)
  let B := (CaseII.F D k).subgroupOf N
  obtain ⟨K, hK, ⟨e⟩⟩ := hF
  have hi : K.index = 16 := by
    rw [hK.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv]
    exact CaseII.F_card D k
  let xN : N := ⟨x, hxF⟩
  obtain ⟨y, hy⟩ := prime_element_conjugate_into K (p := 3) (by rw [hi]; decide)
    xN (by simpa only [← orderOf_coe] using hx)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hy3 : orderOf y = 3 := by
    rw [← orderOf_coe y, ← hg]
    exact ((MulAut.conj g).orderOf_eq xN).trans (by simpa only [← orderOf_coe] using hx)
  obtain ⟨t, ht, hyt⟩ := symmetric_five_three_commutes_involution (e y)
    ((e.orderOf_eq y).trans hy3)
  let u : N := e.symm t
  have hu : orderOf u = 2 := by
    rw [orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hyu : Commute (y : N) u := by
    have h := hyt.map e.symm.toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] at h
    exact congrArg Subtype.val h.eq
  let v := (MulAut.conj g⁻¹) u
  have hv : orderOf v = 2 := (MulAut.conj g⁻¹).orderOf_eq u |>.trans hu
  have hxv : Commute xN v := by
    have h := hyu.map (MulAut.conj g⁻¹).toMonoidHom
    have he : (MulAut.conj g⁻¹) (y : N) = xN := by rw [← hg]; simp only [MulAut.conj_apply]; group
    change Commute ((MulAut.conj g⁻¹) (y : N)) v at h
    rwa [he] at h
  exact ⟨v, by simpa only [orderOf_coe] using hv, congrArg Subtype.val hxv.eq⟩

/-- The actual E-normalizer has at most two conjugacy classes of elements
of order three. The conjugacy relations in the conclusion are internal. -/
public theorem normalizer_E_three_trichotomy
    (hE : ∃ K : Subgroup (normalizer (CaseII.E D k : Set G)),
      ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K ∧
        Nonempty (K ≃* alternatingGroup (Fin 6)))
    (x y z : normalizer (CaseII.E D k : Set G))
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hz : orderOf z = 3) :
    IsConj x y ∨ IsConj x z ∨ IsConj y z := by
  let N := normalizer (CaseII.E D k : Set G)
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  have hi : K.index = 16 := by
    rw [hK.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toEquiv]
    exact CaseII.E_card D k
  have hcop : ¬3 ∣ K.index := by rw [hi]; decide
  obtain ⟨a, ha⟩ := prime_element_conjugate_into K hcop x hx
  obtain ⟨b, hb⟩ := prime_element_conjugate_into K hcop y hy
  obtain ⟨c, hc⟩ := prime_element_conjugate_into K hcop z hz
  have ho {u : N} {v : K} (hv : IsConj u (v : N)) (hu : orderOf u = 3) :
      orderOf (e v) = 3 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hv
    rw [MulEquiv.orderOf_eq, ← orderOf_coe v, ← hg]
    exact ((MulAut.conj g).orderOf_eq u).trans hu
  have lift {u v : K} (h : IsConj (e u) (e v)) : IsConj (u : N) (v : N) := by
    have h' := e.symm.toMonoidHom.map_isConj h
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h'
    exact K.subtype.map_isConj h'
  rcases alternating_six_three_trichotomy (e a) (e b) (e c)
    (ho ha hx) (ho hb hy) (ho hc hz) with h | h | h
  · exact Or.inl (ha.trans ((lift h).trans hb.symm))
  · exact Or.inr (Or.inl (ha.trans ((lift h).trans hc.symm)))
  · exact Or.inr (Or.inr (hb.trans ((lift h).trans hc.symm)))

end Theory.GroupTheory.HeldM22A10.M22Identification
