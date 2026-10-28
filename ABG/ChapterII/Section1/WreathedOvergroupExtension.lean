module
public import ABG.ChapterII.Section1.WreathedOvergroups
public import ABG.ChapterII.Section1.WreathedNonabelianCenter
public import ABG.ChapterII.Section1.NormalQuaternionCenter
public import Mathlib.GroupTheory.PGroup

/-!
# Central-product and extension data for quaternion overgroups

Let X contain the designated maximal quaternion subgroup Y of a wreathed
presentation of height n. Its center has order 2^(r+1) for some r < n.
Either X is the join of Y with its own mapped center, or X is the whole
wreathed group, r = n-1, and that join has index two. In the latter case
the actual element sz lies outside the join and its square generates the
mapped center.

The relations between r and d make every such X nonabelian, so its center
embeds into the cyclic ambient center. Finite two-group center nontriviality
and Lagrange's theorem give the exact radius bound. Proper overgroups use
II.1 Lemma 2(xi); the endpoint X=Y follows by lattice absorption. For the
full group, the normal quaternion subgroup meets the center in order two;
their known cardinalities give index two. The generator relation (sz)^2=u
then supplies the exterior square generator, since Y and sz generate the
whole group.

Source: Alperin–Brauer–Gorenstein II.3 Proposition 3, article pp.25–26,
using II.1 Lemma 2(x), (xi), and (xii), article p.10. The subgroups and
element remain those of the original presentation; no field or Q-group
hypotheses enter this geometry.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem overgroup_noncommutative (X : Subgroup S) (hYX : P.Y ≤ X) :
    ¬ IsMulCommutative X := by
  intro h
  have hr : P.r ∈ X := hYX (Subgroup.subset_closure (by simp))
  have hd : P.d ∈ X := hYX (Subgroup.subset_closure (by simp))
  have hcomm : P.d * P.r = P.r * P.d :=
    congrArg Subtype.val (h.is_comm.comm (⟨P.d, hd⟩ : X) ⟨P.r, hr⟩)
  have hinv : P.r⁻¹ = P.r := by
    rw [← P.d_conj_r, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hsquare : P.r ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [← hinv]
    exact inv_mul_cancel _
  have hord := orderOf_dvd_of_pow_eq_one hsquare
  rw [P.r_order] at hord
  have hlarge : 4 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) P.height
  have := Nat.le_of_dvd (by omega : 0 < 2) hord
  omega

private theorem overgroup_center_power (X : Subgroup S) (hYX : P.Y ≤ X) :
    ∃ r < n, Nat.card (Subgroup.center X) = 2 ^ (r + 1) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hX := P.overgroup_noncommutative X hYX
  let : Nontrivial X := not_subsingleton_iff_nontrivial.mp (by
    intro h
    let := h
    exact hX inferInstance)
  let : Nontrivial (Subgroup.center X) :=
    ((IsPGroup.of_card P.card).to_subgroup X).center_nontrivial
  have hdiv : Nat.card (Subgroup.center X) ∣ 2 ^ n := by
    rw [← P.card_center, ← Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_dvd_of_le (P.nonabelian_center_le X hX)
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hkpos : 0 < k := by
    have := Finite.one_lt_card_iff_nontrivial.mpr
      (inferInstance : Nontrivial (Subgroup.center X))
    by_contra! h
    have hk0 : k = 0 := by omega
    simp [hcard, hk0] at this
  refine ⟨k - 1, by omega, ?_⟩
  simpa only [Nat.sub_add_cancel hkpos] using hcard

private theorem full_center_join_index :
    (P.Y ⊔ Subgroup.center S).index = 2 := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  let : P.Y.Normal := P.quaternion_subgroup.2.2
  have hi : Nat.card (P.Y ⊓ Subgroup.center S : Subgroup S) *
      (Subgroup.center S).relIndex P.Y = Nat.card P.Y := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S)
        (P.Y ⊓ Subgroup.center S) P.Y bot_le inf_le_left
  rw [normal_quaternion_inf_center_card P.Y P.quaternion_subgroup.1,
    P.quaternion_subgroup.2.1, pow_succ] at hi
  have hirel : (Subgroup.center S).relIndex P.Y = 2 ^ n := by omega
  have hb := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S)
    (Subgroup.center S) (P.Y ⊔ Subgroup.center S) bot_le le_sup_right
  simp only [Subgroup.relIndex_bot_left, Subgroup.relIndex_sup_right] at hb
  rw [P.card_center, hirel] at hb
  have hidx := (P.Y ⊔ Subgroup.center S).card_mul_index
  rw [← hb, P.card, show 2 * n + 1 = n + n + 1 by omega,
    pow_succ, pow_add] at hidx
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hidx

/-- Exact center radius and the proper central-product versus full-group
extension alternatives for the actual quaternion overgroup. -/
public theorem overgroup_central_product_extension_data
    (X : Subgroup S) (hYX : P.Y ≤ X) :
    let C := (Subgroup.center X).map X.subtype
    let B := P.Y ⊔ C
    ∃ r < n, Nat.card (Subgroup.center X) = 2 ^ (r + 1) ∧
      (X = B ∨ (X = ⊤ ∧ r = n - 1 ∧ B.relIndex X = 2 ∧
        ∃ a : S, a ∈ X ∧ a ∉ B ∧ Subgroup.zpowers (a ^ 2) = C)) := by
  dsimp only
  obtain ⟨r, hr, hcard⟩ := P.overgroup_center_power X hYX
  refine ⟨r, hr, hcard, ?_⟩
  by_cases htop : X = ⊤
  · right
    have hC : (Subgroup.center X).map X.subtype = Subgroup.center S := by
      apply le_antisymm (P.nonabelian_center_le X (P.overgroup_noncommutative X hYX))
      intro c hc
      refine ⟨⟨c, htop ▸ Subgroup.mem_top c⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro b
      exact Subtype.ext (Subgroup.mem_center_iff.mp hc b)
    have hcn : Nat.card (Subgroup.center X) = 2 ^ n := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, hC, P.card_center]
    have hrn : r = n - 1 := by
      have he : r + 1 = n := Nat.pow_right_injective (by omega : 2 ≤ 2) (hcard.symm.trans hcn)
      omega
    refine ⟨htop, hrn, ?_, P.s * P.z, htop ▸ Subgroup.mem_top _, ?_, ?_⟩
    · rw [hC, htop, Subgroup.relIndex_top_right, P.full_center_join_index]
    · rw [hC]
      intro hv
      have hBtop : P.Y ⊔ Subgroup.center S = ⊤ := by
        apply top_unique
        rw [← P.generator_change.2]
        exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hv)
      have hi := P.full_center_join_index
      rw [hBtop, Subgroup.index_top] at hi
      omega
    · rw [P.sz_sq, hC, P.center_eq_zpowers]
  · left
    by_cases hXY : X = P.Y
    · apply le_antisymm ?_ (sup_le hYX (Subgroup.map_subtype_le _))
      rw [hXY]
      exact le_sup_left
    · exact (P.proper_overgroup X (lt_top_iff_ne_top.mpr htop)
        (lt_of_le_of_ne hYX (Ne.symm hXY))).1

end ABG.Wreathed.Presentation

