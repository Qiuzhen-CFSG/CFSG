module
public import Theory.GroupTheory.PResidual.OrderSix
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega

/-!
# Point stabilizers with nonnormal residual in binary Omega

A subgroup of order six with nonnormal two-residual fixes a nonsingular
vector in the genuine natural action of Ω₄⁺(2). The cubic residual is
cyclic; if it were fixed-point-free, the coordinate action would normalize
it. A normalizing involution and the cubic therefore have a common
nonsingular fixed vector. They generate the subgroup, whose order equals
the full point stabilizer's order.

All finite identities use the proved coordinates on quadratic isometries.
This supplies the point marking for Aschbacher--Smith 15.2.18(3ii),
printed p.1113, while retaining the literal natural action.
-/

open Subgroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

private def cube (k : Code) : Prop := ∀ v : Space, eval k (eval k (eval k v)) = v
private instance (k : Code) : Decidable (cube k) := inferInstanceAs (Decidable (∀ _, _))
private def nontrivial (k : Code) : Prop := ∃ v : Space, eval k v ≠ v
private instance (k : Code) : Decidable (nontrivial k) := inferInstanceAs (Decidable (∃ _, _))
private def fixedFree (k : Code) : Prop := ∀ v : Space, eval k v = v → v = 0
private instance (k : Code) : Decidable (fixedFree k) := inferInstanceAs (Decidable (∀ _, _))
private def normalizeCube (j k : Code) : Prop :=
  (∀ v : Space, eval j (eval k v) = eval k (eval j v)) ∨
  (∀ v : Space, eval j (eval k v) = eval k (eval k (eval j v)))
private instance (j k : Code) : Decidable (normalizeCube j k) :=
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000 in
private theorem fixedFree_normal_table : ∀ k : Code, cube k → fixedFree k →
    ∀ j : Code, j.1.2 = j.2.1.2 → normalizeCube j k := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem nontrivial_fixed_table : ∀ k : Code, cube k → nontrivial k →
    ¬ fixedFree k → ∀ j : Code, (∀ v : Space, eval j (eval j v) = v) →
      normalizeCube j k → ∃ v : Space, q v = 1 ∧ eval k v = v ∧ eval j v = v := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem nonsingular_stabilizer_table : ∀ v : Space, q v = 1 →
    Fintype.card {j : Code // j.1.2 = j.2.1.2 ∧ eval j v = v} = 6 := by
  decide +kernel

private theorem fixedFree_zpowers_normal (a : omega) (ha : a^3=1)
    (hf : ∀ v : Space, a • v = v → v=0) : (zpowers a).Normal := by
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective a.val
  have hc : cube k := by
    intro v
    have he := congrArg (fun g : omega => g.val.val v) ha
    change a.val.val (a.val.val (a.val.val v)) = v at he
    rw [←hk] at he
    simpa only [codeMap,candidate_eval] using he
  have hfree : fixedFree k := by
    intro v hv
    apply hf v
    change a.val.val v = v
    rw [←hk]
    exact (candidate_eval k v).trans hv
  apply normal_iff_map_conj_eq.mpr
  intro g
  rw [MonoidHom.map_zpowers]
  change zpowers (g*a*g⁻¹) = zpowers a
  obtain ⟨j,hj⟩ := codeMap_bijective.surjective g.val
  have hb := (codeMap_mem_omega j).mp (hj.symm ▸ g.property)
  rcases fixedFree_normal_table k hc hfree j hb with hcomm | hinv
  · have he : g*a = a*g := by
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change g.val.val (a.val.val v) = a.val.val (g.val.val v)
      rw [←hk,←hj]
      simpa only [codeMap,candidate_eval] using hcomm v
    rw [he,mul_inv_cancel_right]
  · have he : g*a = (a*a)*g := by
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change g.val.val (a.val.val v) = a.val.val (a.val.val (g.val.val v))
      rw [←hk,←hj]
      simpa only [codeMap,candidate_eval] using hinv v
    have hi : a*a = a⁻¹ := (inv_eq_of_mul_eq_one_right (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using ha)).symm
    rw [he,mul_inv_cancel_right,hi,zpowers_inv]

private theorem omega_nonsingular_stabilizer_card (v : Space) (hv : form v = 1) :
    Nat.card (MulAction.stabilizer omega v) = 6 := by
  let B : Code → Prop := fun j => j.1.2 = j.2.1.2
  let e : {j : Code // B j} ≃ omega :=
    codeEquiv.subtypeEquiv (fun j => (codeMap_mem_omega j).symm)
  let f : {j : Code // B j ∧ eval j v = v} ≃ MulAction.stabilizer omega v :=
    (Equiv.subtypeSubtypeEquivSubtypeInter B (fun j => eval j v = v)).symm.trans
      (e.subtypeEquiv (fun j => by
        change eval j.val v = v ↔ (codeMap j.val).val v = v
        rw [show (codeMap j.val).val v = eval j.val v from candidate_eval j.val v]))
  rw [←Nat.card_congr f,Nat.card_eq_fintype_card]
  exact nonsingular_stabilizer_table v hv

private theorem cubic_involution_sup_eq (N : Subgroup omega) (hN : Nat.card N = 6)
    (a b : omega) (ha : a ∈ N) (hb : b ∈ N)
    (hao : orderOf a = 3) (hbo : orderOf b = 2) : zpowers a ⊔ zpowers b = N := by
  let D := zpowers a ⊔ zpowers b
  have hd : D ≤ N := sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  have h3 : 3 ∣ Nat.card D := by
    have hh := card_dvd_of_le (show zpowers a ≤ D from le_sup_left)
    simpa only [Nat.card_zpowers,hao] using hh
  have h2 : 2 ∣ Nat.card D := by
    have hh := card_dvd_of_le (show zpowers b ≤ D from le_sup_right)
    simpa only [Nat.card_zpowers,hbo] using hh
  have hpos := Nat.card_pos (α := D)
  have h6 : 6 ∣ Nat.card D :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
  apply eq_of_le_of_card_ge hd
  rw [hN]
  exact Nat.le_of_dvd hpos h6

private theorem cubic_powers_cases {D : Type*} [Group D] [Finite D]
    (a x : D) (ha : orderOf a = 3) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a ∨ x = a^2 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ha] at hx
  obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hx
  have hi3 := Finset.mem_range.mp hi
  interval_cases i <;> simp_all

/-- The actual natural action marks a nonnormal-residual subgroup of order six
as the full stabilizer of a nonsingular vector. -/
public theorem point_stabilizer_of_nonnormal_residual (N : Subgroup omega)
    (hN : Nat.card N = 6) (hn : ¬ ((pResidual 2 N).map N.subtype).Normal)
    (b : omega) (hb : b ∈ N) (hbo : orderOf b = 2) :
    ∃ v : Space, form v = 1 ∧ b • v = v ∧ N = MulAction.stabilizer omega v := by
  let R := (pResidual 2 N).map N.subtype
  have hR : Nat.card R = 3 := by
    rw [card_map_of_injective N.subtype_injective]
    exact card_twoResidual_of_card_six hN
  have hRne : R ≠ ⊥ := by intro he; rw [he,card_bot] at hR; contradiction
  obtain ⟨a,ha,hane⟩ := R.bot_or_exists_ne_one.resolve_left hRne
  have ha3 : a^3=1 := by
    have h := pow_card_eq_one' (x := (⟨a,ha⟩ : R))
    rw [hR] at h
    exact congrArg Subtype.val h
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 hane
  have hpow : zpowers a = R := eq_of_le_of_card_ge (zpowers_le.mpr ha)
    (by rw [Nat.card_zpowers,hao,hR])
  have hnorm : N ≤ normalizer (R : Set omega) := by
    have hh := (pResidual 2 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hconj : b*a*b⁻¹ ∈ zpowers a := hpow.symm ▸
    (mem_normalizer_iff.mp (hnorm hb) a).mp ha
  have hba : b*a = a*b ∨ b*a = (a*a)*b := by
    rcases cubic_powers_cases a (b*a*b⁻¹) hao hconj with he | he | he
    · have hh := mul_inv_eq_iff_eq_mul.mp he
      have ha1 : a = 1 := by
        apply mul_left_cancel (a := b)
        simpa using hh
      exact (hane ha1).elim
    · exact Or.inl (mul_inv_eq_iff_eq_mul.mp he)
    · exact Or.inr (by simpa only [pow_two] using mul_inv_eq_iff_eq_mul.mp he)
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective a.val
  obtain ⟨j,hj⟩ := codeMap_bijective.surjective b.val
  have hc : cube k := by
    intro v
    have he := congrArg (fun g : omega => g.val.val v) ha3
    change a.val.val (a.val.val (a.val.val v)) = v at he
    rw [←hk] at he
    simpa only [codeMap,candidate_eval] using he
  have hnt : nontrivial k := by
    change ∃ v : Space, eval k v ≠ v
    by_contra! h
    apply hane
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change a.val.val v = v
    rw [←hk]
    exact (candidate_eval k v).trans (h v)
  have hnf : ¬ fixedFree k := by
    intro hf
    apply hn
    change R.Normal
    rw [←hpow]
    apply fixedFree_zpowers_normal a ha3
    intro v hv
    apply hf v
    change a.val.val v = v at hv
    rw [←hk] at hv
    exact (candidate_eval k v).symm.trans hv
  have hj2 : ∀ v : Space, eval j (eval j v) = v := by
    intro v
    have h2 : b^2=1 := by simpa only [hbo] using pow_orderOf_eq_one b
    have hh := congrArg (fun g : omega => g.val.val v) h2
    change b.val.val (b.val.val v)=v at hh
    rw [←hj] at hh
    simpa only [codeMap,candidate_eval] using hh
  have hjk : normalizeCube j k := by
    rcases hba with he | he
    · left
      intro v
      have hh := congrArg (fun g : omega => g.val.val v) he
      change b.val.val (a.val.val v) = a.val.val (b.val.val v) at hh
      rw [←hk,←hj] at hh
      simpa only [codeMap,candidate_eval] using hh
    · right
      intro v
      have hh := congrArg (fun g : omega => g.val.val v) he
      change b.val.val (a.val.val v) = a.val.val (a.val.val (b.val.val v)) at hh
      rw [←hk,←hj] at hh
      simpa only [codeMap,candidate_eval] using hh
  obtain ⟨v,hv,hav,hbv⟩ := nontrivial_fixed_table k hc hnt hnf j hj2 hjk
  have hav' : a • v = v := by
    change a.val.val v = v
    rw [←hk]
    exact (candidate_eval k v).trans hav
  have hbv' : b • v = v := by
    change b.val.val v = v
    rw [←hj]
    exact (candidate_eval j v).trans hbv
  refine ⟨v,hv,hbv',?_⟩
  have hle : N ≤ MulAction.stabilizer omega v := by
    rw [←cubic_involution_sup_eq N hN a b (map_subtype_le _ ha) hb hao hbo]
    exact sup_le (zpowers_le.mpr hav') (zpowers_le.mpr hbv')
  exact eq_of_le_of_card_ge hle (by rw [hN,omega_nonsingular_stabilizer_card v hv])

end OrthogonalFourBinary.SylowGeometry
