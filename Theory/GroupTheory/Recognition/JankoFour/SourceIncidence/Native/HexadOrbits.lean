module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbitCertificate

/-!
# Native rank-three hexad action

The checked transport forest supplies actual M₂₂ elements fixing one hexad
and moving any two hexads with the same intersection size. The literal
77-hexad enumeration gives subdegrees 1, 60, and 16. These facts are consumed
by the ambient plane chart, with no ambient plane uniqueness assumption.
Source: Aschbacher–Segev (1991), (5.3)(1), p.600.
-/
public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
open Sporadic.Mathieu SourceCycleBase
open scoped Pointwise

theorem forest_step (i : Fin 77) (hi : depth i ≠ 0) :
    generator (letter i) • m22BlockAt (parent i) = m22BlockAt i := by
  apply m22Perm_smul_blockAt_of_bits
  intro x
  have hh := (forest i).2 hi |>.2.2 ((generator (letter i)).val.symm x)
  simpa only [←generator_apply,Equiv.apply_symm_apply] using hh

theorem exists_transport (i : Fin 77) : ∃ g : M22,
    g • m22Hexad123 = m22Hexad123 ∧ g • m22BlockAt (root i) = m22BlockAt i := by
  generalize hn : depth i = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hz : depth i = 0
    · refine ⟨1,one_smul _ _,?_⟩
      rw [one_smul,←(forest i).1 hz]
    · obtain ⟨g,hg,hgi⟩ := ih (depth (parent i)) (by have := ((forest i).2 hz).1; omega) (parent i) rfl
      refine ⟨generator (letter i)*g,?_,?_⟩
      · rw [mul_smul,hg,generator_fixes]
      · rw [mul_smul,←((forest i).2 hz).2.1,hgi]
        exact forest_step i hz

private theorem hexad_index (B : Hexad) : ∃ i, m22BlockAt i = B.val := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp B.property
  exact ⟨i,hi⟩

theorem standard_transitive (B C : Hexad)
    (he : (B.val ∩ m22Hexad123).card = (C.val ∩ m22Hexad123).card) :
    ∃ g : M22, g • m22Hexad123 = m22Hexad123 ∧ g • B.val = C.val := by
  obtain ⟨i,hi⟩ := hexad_index B
  obtain ⟨j,hj⟩ := hexad_index C
  have hr : root i = root j := by rw [root_card,root_card,hi,hj,he]
  obtain ⟨g,hg,hgi⟩ := exists_transport i
  obtain ⟨k,hk,hkj⟩ := exists_transport j
  refine ⟨k*g⁻¹,?_,?_⟩
  · rw [mul_smul,inv_smul_eq_iff.mpr hg.symm,hk]
  · rw [←hi,←hgi,mul_smul,inv_smul_smul,hr,hkj,hj]

theorem inter_card_smul (g : M22) (B C : Finset (Fin 22)) :
    ((g • B) ∩ (g • C)).card = (B ∩ C).card := by
  rw [←Finset.smul_finset_inter,Finset.card_smul_finset]

@[expose] noncomputable def smulHexad (g : M22) (B : Hexad) : Hexad :=
  ⟨g • B.val,m22_smul_block_mem g B.val B.property⟩

theorem transitive (A B C : Hexad)
    (he : (B.val ∩ A.val).card = (C.val ∩ A.val).card) :
    ∃ g : M22, g • A.val = A.val ∧ g • B.val = C.val := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq A.property
  have he' : ((smulHexad k⁻¹ B).val ∩ m22Hexad123).card =
      ((smulHexad k⁻¹ C).val ∩ m22Hexad123).card := by
    change ((k⁻¹ • B.val) ∩ m22Hexad123).card = ((k⁻¹ • C.val) ∩ m22Hexad123).card
    rw [←inv_smul_eq_iff.mpr hk.symm,inter_card_smul,inter_card_smul,he]
  obtain ⟨g,hg,hgBC⟩ := standard_transitive (smulHexad k⁻¹ B) (smulHexad k⁻¹ C) he'
  refine ⟨k*g*k⁻¹,?_,?_⟩
  · rw [mul_smul,mul_smul,←hk,inv_smul_smul,hg]
  · change g • (k⁻¹ • B.val) = k⁻¹ • C.val at hgBC
    rw [mul_smul,mul_smul,hgBC,smul_inv_smul]

theorem cases (A B : Hexad) :
    (B.val ∩ A.val).card = 0 ∨ (B.val ∩ A.val).card = 2 ∨ B = A := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq A.property
  obtain ⟨i,hi⟩ := hexad_index (smulHexad k⁻¹ B)
  have hc : (m22BlockAt i ∩ m22Hexad123).card = (B.val ∩ A.val).card := by
    rw [hi]
    change ((k⁻¹ • B.val) ∩ m22Hexad123).card = _
    rw [←inv_smul_eq_iff.mpr hk.symm,inter_card_smul]
  rcases intersection_cases i with h0 | h2 | h6
  · exact Or.inl (hc.symm.trans h0)
  · exact Or.inr (Or.inl (hc.symm.trans h2))
  · right; right
    apply Subtype.ext
    have h := congrArg (k • ·) (hi.symm.trans h6)
    exact (smul_inv_smul k B.val).symm.trans (h.trans hk)

noncomputable def indexEquiv : Fin 77 ≃ Hexad := by
  let f : Fin 77 → Hexad := fun i => ⟨m22BlockAt i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hs : Function.Surjective f := by
    intro B; obtain ⟨i,hi⟩ := hexad_index B; exact ⟨i,Subtype.ext hi⟩
  exact Equiv.ofBijective f (hs.bijective_of_nat_card_le (by
    rw [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_coe,m22Blocks_cardinality]))

theorem indexEquiv_val (i : Fin 77) : (indexEquiv i).val = m22BlockAt i := by
  simp [indexEquiv]

theorem root_one (i : Fin 77) : root i = 1 ↔ (m22BlockAt i ∩ m22Hexad123).card = 2 := by
  rw [root_card]
  split_ifs <;> simp_all

theorem root_fortynine (i : Fin 77) : root i = 49 ↔ (m22BlockAt i ∩ m22Hexad123).card = 0 := by
  rw [root_card]
  rcases intersection_cases i with h0 | h2 | h6
  · simp [h0]
  · simp [h2]
  · rw [h6]
    have hc : m22Hexad123.card = 6 := m22Block_card _ m22Hexad123_mem
    simp [hc]

private noncomputable def smulEquiv (g : M22) : Hexad ≃ Hexad where
  toFun := smulHexad g
  invFun := smulHexad g⁻¹
  left_inv B := Subtype.ext (inv_smul_smul g B.val)
  right_inv B := Subtype.ext (smul_inv_smul g B.val)

theorem intersection_card (A : Hexad) (r : Nat) :
    Nat.card {B : Hexad // (B.val ∩ A.val).card = r} =
      Nat.card {B : Hexad // (B.val ∩ m22Hexad123).card = r} := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq A.property
  apply Nat.card_congr
  apply (smulEquiv k⁻¹).subtypeEquiv
  intro B
  change (B.val ∩ A.val).card = r ↔ ((k⁻¹ • B.val) ∩ m22Hexad123).card = r
  rw [←inv_smul_eq_iff.mpr hk.symm,inter_card_smul]

theorem neighbor_card (A : Hexad) : Nat.card {B : Hexad // (B.val ∩ A.val).card = 2} = 60 := by
  rw [intersection_card A 2]
  rw [←Nat.card_congr (indexEquiv.subtypeEquiv (p := fun i => root i = 1)
    (q := fun B => (B.val ∩ m22Hexad123).card = 2) root_one)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact root_sizes.1

theorem nonneighbor_card (A : Hexad) : Nat.card {B : Hexad // (B.val ∩ A.val).card = 0} = 16 := by
  rw [intersection_card A 0]
  rw [←Nat.card_congr (indexEquiv.subtypeEquiv (p := fun i => root i = 49)
    (q := fun B => (B.val ∩ m22Hexad123).card = 0) root_fortynine)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact root_sizes.2

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
