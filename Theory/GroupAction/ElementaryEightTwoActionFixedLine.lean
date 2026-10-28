module
public import Theory.GroupAction.ElementaryEightInvolution
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Elementary two-automorphisms of an eight with a fixed line

An elementary abelian two-subgroup of the automorphism group of an elementary
abelian group of order eight, with common fixed subgroup of order two, has
order four. Every displacement lies in that common fixed subgroup.

A nonidentity involution fixes four elements by the existing involution theorem.
The kernel/image cardinality formula makes its displacement image a subgroup
of order two. Commuting automorphisms preserve this image and therefore fix it
pointwise. Burnside's lemma expresses the fixed-point sum as `4 * |B| + 4`,
so the actor order divides four. Orders one and two contradict the common
fixed-subgroup hypothesis.

This is the elementary transvection calculation used to recognize the two
order-eight factors in the extraspecial case of Stellmacher (9.1), Journal
of Algebra 190 (1997), p.48; see `refs/latex/stellmacher-n-group.tex`.
It needs only the stated elementary-group and fixed-point hypotheses.
-/

open scoped IsMulCommutative
universe u

private theorem involution_data {E : Type u} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (a : MulAut E) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nat.card (MulAction.fixedBy E a) = 4 ∧
    ∃ D : Subgroup E, Nat.card D = 2 ∧
      (∀ x : E, x⁻¹ * a x ∈ D) ∧
      (∀ z ∈ D, ∃ x : E, x⁻¹ * a x = z) := by
  classical
  let Q := Subgroup.zpowers a
  let aq : Q := ⟨a, Subgroup.mem_zpowers a⟩
  have haq : aq ≠ 1 ∧ aq ^ 2 = 1 := by
    constructor
    · intro h; exact ha (congrArg Subtype.val h)
    · exact Subtype.ext ha2
  have hQ : Nat.card Q = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha]
  have hmove : ∃ x : E, aq • x ≠ x := by
    by_contra! h
    apply ha
    ext x
    exact h x
  have hc := fixed_subgroup_card_four_of_nontrivial_involution_on_eight aq haq hQ hE hmove
  let d : E →* E := {
    toFun := fun x => x⁻¹ * a x
    map_one' := by simp
    map_mul' := by intro x y; simp only [mul_inv_rev, map_mul]; ac_rfl }
  have hker : d.ker = FixedPoints.subgroup Q E := by
    ext x
    change (x⁻¹ * a x = 1) ↔ ∀ q : Q, q • x = x
    constructor
    · intro h q
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp q.property
      change (q : MulAut E) x = x
      rw [← hn]
      exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy E a from
        (inv_mul_eq_one.mp h).symm) n
    · intro h
      exact inv_mul_eq_one.mpr (h aq).symm
  have he : (FixedPoints.subgroup Q E) ≃ MulAction.fixedBy E a := {
    toFun := fun x => ⟨x.val, x.property aq⟩
    invFun := fun x => ⟨x.val, by
      intro q
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp q.property
      change (q : MulAut E) x.val = x.val
      rw [← hn]
      exact MulAction.mem_fixedBy_zpow x.property n⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨(Nat.card_congr he).symm.trans hc, d.range, ?_, ?_, ?_⟩
  · have hm := d.ker.card_mul_index
    rw [Subgroup.index_ker, hker, hc, hE] at hm
    omega
  · intro x; exact ⟨x, rfl⟩
  · intro z hz; exact hz

/-- An elementary two-group of automorphisms of an eight with a common fixed
line has order four, and all its displacements lie on that fixed line. -/
public theorem elementaryEight_two_action_fixed_line
    {E : Type u} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E)) [IsElementaryAbelian 2 B]
    (hfix : Nat.card (FixedPoints.subgroup B E) = 2) :
    Nat.card B = 4 ∧ ∀ (b : B) (e : E), e⁻¹ * (b : MulAut E) e ∈ FixedPoints.subgroup B E := by
  classical
  have hsquare (b : B) : (b : MulAut E) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian b.val b.property
  have hdata (b : B) (hb : b ≠ 1) :=
    involution_data hE b.val (fun h => hb (Subtype.ext h)) (hsquare b)
  have hdisplace : ∀ (b : B) (e : E), e⁻¹ * (b : MulAut E) e ∈ FixedPoints.subgroup B E := by
    intro b e
    by_cases hb : b = 1
    · subst b; simp
    obtain ⟨_, D, hD, hmem, hsurj⟩ := hdata b hb
    have hcomm (c : B) (x : E) : (c : MulAut E) ((b : MulAut E) x) =
        (b : MulAut E) ((c : MulAut E) x) :=
      congrArg (fun q : B => (q : MulAut E) x) (mul_comm c b)
    have hpres (c : B) (z : E) (hz : z ∈ D) : (c : MulAut E) z ∈ D := by
      obtain ⟨x, rfl⟩ := hsurj z hz
      simpa only [map_mul, map_inv, hcomm] using hmem ((c : MulAut E) x)
    intro c
    let z : D := ⟨e⁻¹ * (b : MulAut E) e, hmem e⟩
    let w : D := ⟨(c : MulAut E) z.val, hpres c z.val z.property⟩
    change w.val = z.val
    by_cases hz : z = 1
    · change (c : MulAut E) z.val = z.val
      simp [hz]
    have hw : w ≠ 1 := by
      intro hw
      apply hz
      apply Subtype.ext
      exact (c : MulAut E).injective ((congrArg Subtype.val hw).trans (map_one _).symm)
    obtain ⟨t, _, ht⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hD
    exact congrArg Subtype.val ((ht w hw).trans (ht z hz).symm)
  refine ⟨?_, hdisplace⟩
  let : Fintype E := Fintype.ofFinite E
  let : Fintype B := Fintype.ofFinite B
  let : Fintype (Quotient (MulAction.orbitRel B E)) := Fintype.ofFinite _
  have hc (b : B) : Fintype.card (MulAction.fixedBy E b) =
      4 + if b = 1 then 4 else 0 := by
    by_cases hb : b = 1
    · subst b
      rw [if_pos rfl]
      have he : MulAction.fixedBy E (1 : B) ≃ E := {
        toFun := Subtype.val
        invFun := fun x => ⟨x, one_smul B x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      rw [Fintype.card_congr he, ← Nat.card_eq_fintype_card, hE]
    · rw [if_neg hb, add_zero, ← Nat.card_eq_fintype_card]
      have he : MulAction.fixedBy E b ≃ MulAction.fixedBy E (b : MulAut E) :=
        Equiv.subtypeEquivRight (fun _ => Iff.rfl)
      rw [Nat.card_congr he, (hdata b hb).1]
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B E
  simp_rw [hc] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  have hdiv : Nat.card B ∣ 4 := by
    rw [Nat.card_eq_fintype_card]
    have hd : Fintype.card B ∣ Fintype.card B * 4 + 4 :=
      hsum ▸ dvd_mul_left (Fintype.card B) _
    exact (Nat.dvd_add_iff_right (dvd_mul_right (Fintype.card B) 4)).mpr hd
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hBle : Nat.card B ≤ 4 := Nat.le_of_dvd (by decide) hdiv
  have hnot1 : Nat.card B ≠ 1 := by
    intro hB
    have : Subsingleton B := Finite.card_le_one_iff_subsingleton.mp (by omega)
    have ht : FixedPoints.subgroup B E = ⊤ := by
      ext x
      simp only [Subgroup.mem_top, iff_true]
      intro b
      rw [Subsingleton.elim b 1, one_smul]
    rw [ht, Subgroup.card_top, hE] at hfix
    omega
  have hnot2 : Nat.card B ≠ 2 := by
    intro hB
    obtain ⟨b, hb, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
    have he : FixedPoints.subgroup B E ≃ MulAction.fixedBy E b := {
      toFun := fun x => ⟨x.val, x.property b⟩
      invFun := fun x => ⟨x.val, by
        intro c
        by_cases hc : c = 1
        · rw [hc, one_smul]
        · rw [huniq c hc]; exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hh := Nat.card_congr he
    rw [hfix, Nat.card_eq_fintype_card, hc, if_neg hb] at hh
    omega
  interval_cases hB : Nat.card B <;> omega
