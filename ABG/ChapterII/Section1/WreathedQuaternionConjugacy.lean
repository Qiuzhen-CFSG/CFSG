module
public import ABG.ChapterII.Section1.WreathedQuaternionUnique
public import ABG.ChapterII.Section1.WreathedExceptionalDefs
public import Theory.GroupTheory.CyclicTwoSubgroups

/-!
# Conjugacy of quaternion subgroups in a wreathed group

Every quaternion subgroup of order eight in a chosen wreathed presentation
is conjugate to `quaternionCore = ⟨r^(2^(n-2)),d⟩`. This supplies the quaternion
part of ABG Chapter II §1 Lemma 3(iii), article p.10. The presentation retains
height `n≥2` and its prescribed cardinality; the proof includes `n=2`.

The established quaternion containment theorem places the subgroup in `Y`.
The cyclic rotation subgroup `⟨r⟩` has index two in `Y`, so its intersection
with a quaternion subgroup has order four: a quaternion subgroup cannot lie
in a cyclic group. The cyclic-two-subgroup theorem identifies this
intersection as `⟨r^(2^(n-2))⟩`. Quaternion normal forms then give generators
`r^(2^(n-2))` and `r^i*d`. Conjugation by `s^i` fixes `r` and sends `d` to
`r^i*d`, proving the asserted ambient conjugacy. All subgroups and generators
are the actual ones in the chosen presentation.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : ABG.Wreathed.Presentation S n)

private theorem Y_normal_form {g : S} (hg : g ∈ P.Y) :
    ∃ i : ℤ, g = P.r ^ i ∨ g = P.r ^ i * P.d := by
  have hi : P.r⁻¹ = P.r ^ (2 ^ n - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) n)), ← P.r_order, pow_orderOf_eq_one]
  exact ABG.QuasiDihedral.square_normal_form_int P.r P.d (2 ^ n - 1)
    ((2 ^ (n - 1) : ℕ) : ℤ) (by simpa only [zpow_natCast] using P.d_sq) (P.d_conj_r.trans hi) g hg

private theorem rotation_relIndex : (Subgroup.zpowers P.r).relIndex P.Y = 2 := by
  have hrY : Subgroup.zpowers P.r ≤ P.Y :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have he := Subgroup.subgroupOfEquivOfLe hrY
  have hc : Nat.card ((Subgroup.zpowers P.r).subgroupOf P.Y) = 2 ^ n := by
    rw [Nat.card_congr he.toEquiv, Nat.card_zpowers, P.r_order]
  have hh := ((Subgroup.zpowers P.r).subgroupOf P.Y).card_mul_index
  rw [hc, P.quaternion_subgroup.2.1, pow_succ] at hh
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hh

private theorem quaternion_not_le_rotation (Q : Subgroup S)
    (e : Q ≃* QuaternionGroup 2) : ¬Q ≤ Subgroup.zpowers P.r := by
  intro hh
  let f := Q.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.symm.injective
  have ha : f (QuaternionGroup.a 1) ∈ Subgroup.zpowers P.r := hh (e.symm _).property
  have hb : f (QuaternionGroup.xa 0) ∈ Subgroup.zpowers P.r := hh (e.symm _).property
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hc : Commute (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) := by
    rw [← hi, ← hj]
    exact (Commute.refl P.r).zpow_zpow i j
  have hbad : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply hf
    simpa only [map_mul] using hc.eq
  revert hbad
  decide

private theorem rotation_intersection_card (Q : Subgroup S)
    (e : Q ≃* QuaternionGroup 2) : Nat.card ↥(Q ⊓ Subgroup.zpowers P.r) = 4 := by
  have hQY := P.quaternion_le_Y Q ⟨1, by decide, ⟨by simpa using e⟩⟩
  have hcardQ : Nat.card Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  let : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have hidxle := Subgroup.relIndex_le_of_le_right hQY (show (Subgroup.zpowers P.r).relIndex P.Y ≠ 0 by rw [P.rotation_relIndex]; decide)
  have hidxne : (Subgroup.zpowers P.r).relIndex Q ≠ 1 := by
    intro hh
    exact P.quaternion_not_le_rotation Q e (Subgroup.relIndex_eq_one.mp hh)
  have hidx0 : (Subgroup.zpowers P.r).relIndex Q ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hidx : (Subgroup.zpowers P.r).relIndex Q = 2 := by
    rw [P.rotation_relIndex] at hidxle
    omega
  have hcard := ((Q ⊓ Subgroup.zpowers P.r).subgroupOf Q).card_mul_index
  have he := Subgroup.subgroupOfEquivOfLe (show Q ⊓ Subgroup.zpowers P.r ≤ Q from inf_le_left)
  rw [Nat.card_congr he.toEquiv, hcardQ] at hcard
  change Nat.card ↥(Q ⊓ Subgroup.zpowers P.r) * (Q ⊓ Subgroup.zpowers P.r).relIndex Q = 8 at hcard
  rw [Subgroup.inf_relIndex_left, hidx] at hcard
  omega


private theorem rotation_intersection (Q : Subgroup S)
    (e : Q ≃* QuaternionGroup 2) :
    Q ⊓ Subgroup.zpowers P.r = Subgroup.zpowers (P.r ^ (2 ^ (n - 2))) := by
  obtain ⟨k, hkn, he⟩ := Subgroup.eq_zpowers_two_pow_of_le
    (show P.r ^ (2 ^ n) = 1 by rw [← P.r_order]; exact pow_orderOf_eq_one _)
    (Q ⊓ Subgroup.zpowers P.r) inf_le_right
  have hc := P.rotation_intersection_card Q e
  rw [he, Nat.card_zpowers, orderOf_pow_of_dvd (by positivity)
    (by rw [P.r_order]; exact Nat.pow_dvd_pow 2 hkn), P.r_order,
    Nat.pow_div hkn (by decide)] at hc
  have heq : n - k = 2 := Nat.pow_right_injective (a := 2) (by decide) (by simpa using hc)
  have hk : k = n - 2 := by omega
  simpa only [hk] using he

private theorem quaternion_generators (Q : Subgroup S)
    (e : Q ≃* QuaternionGroup 2) :
    ∃ i : ℤ, Q = Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) := by
  have hQY := P.quaternion_le_Y Q ⟨1, by decide, ⟨by simpa using e⟩⟩
  have hnot := P.quaternion_not_le_rotation Q e
  obtain ⟨q, hqQ, hqR⟩ := Set.not_subset.mp hnot
  obtain ⟨i, hi | rfl⟩ := P.Y_normal_form (hQY hqQ)
  · exact (hqR ⟨i, hi.symm⟩).elim
  · refine ⟨i, ?_⟩
    have hrot := P.rotation_intersection Q e
    have hrotQ : Subgroup.zpowers (P.r ^ (2 ^ (n - 2))) ≤ Q := by
      rw [← hrot]
      exact inf_le_left
    apply le_antisymm
    · intro g hg
      obtain ⟨j, rfl | rfl⟩ := P.Y_normal_form (hQY hg)
      · apply (show Subgroup.zpowers (P.r ^ (2 ^ (n - 2))) ≤
            Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) from
          Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
        rw [← hrot]
        exact ⟨hg, ⟨j, rfl⟩⟩
      · have hdiff : P.r ^ (j - i) ∈ Q ⊓ Subgroup.zpowers P.r := by
          refine ⟨?_, ⟨j - i, rfl⟩⟩
          have hh := Q.mul_mem hg (Q.inv_mem hqQ)
          change P.r ^ (j - i) ∈ Q
          simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, zpow_sub] using hh
        have hm : P.r ^ (j - i) ∈ Subgroup.closure
            ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) := by
          have hle : Subgroup.zpowers (P.r ^ (2 ^ (n - 2))) ≤
            Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) :=
              Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
          exact hle (hrot ▸ hdiff)
        have hh := (Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S)).mul_mem
          hm (Subgroup.subset_closure (show P.r ^ i * P.d ∈
            ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) by simp))
        simpa only [← mul_assoc, ← zpow_add, sub_add_cancel] using hh
    · apply (Subgroup.closure_le Q).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hrotQ (Subgroup.mem_zpowers _)
      · exact hqQ


private theorem s_zpow_conj_r (i : ℤ) :
    (MulAut.conj (P.s ^ i)) P.r = P.r := by
  have hc : Commute P.s P.r :=
    (Commute.refl P.s).mul_right (show Commute P.s P.t from P.commute).inv_right
  change P.s ^ i * P.r * (P.s ^ i)⁻¹ = P.r
  rw [(hc.zpow_left i).eq]
  group

private theorem s_zpow_conj_d (i : ℤ) :
    (MulAut.conj (P.s ^ i)) P.d = P.r ^ i * P.d := by
  have hst : Commute P.s P.t := P.commute
  have hswap : P.z * P.s ^ (-i) = P.t ^ (-i) * P.z :=
    (show SemiconjBy P.z P.s P.t from P.z_mul_s).zpow_right (-i)
  have hrpow : P.r ^ i = P.s ^ i * P.t ^ (-i) := by
    simp only [r, hst.inv_right.mul_zpow, inv_zpow, zpow_neg]
  have hc : Commute P.x₂ (P.t ^ (-i)) := (hst.pow_left _).zpow_right _
  change P.s ^ i * P.d * (P.s ^ i)⁻¹ = _
  calc
    _ = P.s ^ i * P.x₂ * (P.z * P.s ^ (-i)) := by simp only [d, zpow_neg]; group
    _ = P.s ^ i * P.x₂ * (P.t ^ (-i) * P.z) := by rw [hswap]
    _ = P.s ^ i * (P.x₂ * P.t ^ (-i)) * P.z := by group
    _ = P.s ^ i * (P.t ^ (-i) * P.x₂) * P.z := by rw [hc.eq]
    _ = P.r ^ i * P.d := by rw [hrpow]; dsimp [d]; group


private theorem quaternion_map (i : ℤ) :
    (Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.d} : Set S)).map
        (MulAut.conj (P.s ^ i)).toMonoidHom =
      Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.r ^ i * P.d} : Set S) := by
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom, map_pow,
    P.s_zpow_conj_r, P.s_zpow_conj_d]


/-- Every quaternion subgroup of order eight is conjugate to the chosen core. -/
public theorem quaternion_subgroup_conjugacy (Q : Subgroup S)
    (hQ : ABG.IsQuaternionGroup Q) :
    ∃ g : S, P.quaternionCore.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨e⟩ := hQ
  obtain ⟨i, hi⟩ := P.quaternion_generators Q e
  refine ⟨P.s ^ i, ?_⟩
  change (Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.d} : Set S)).map
    (MulAut.conj (P.s ^ i)).toMonoidHom = Q
  rw [P.quaternion_map, ← hi]

end ABG.Wreathed.Presentation
