module
public import ABG.ChapterII.Section3.QSylowGeometry
public import ABG.ChapterII.Section2.WeakCenterTransport

/-!
# Four-subgroup involutions cannot all fuse in a Q-group

In every finite enlarged Q-group, the three nonidentity elements of an
arbitrary Klein-four subgroup are not all ambient-conjugate. No full Sylow
shape or characteristic-power assumption is imposed.

Place the four-subgroup in a Sylow two-subgroup. The enlarged-Q geometry
makes its intersection with the Sylow center nontrivial. The resulting
central involution generates a weakly closed subgroup of order two, so any
ambient conjugate still lying in that Sylow subgroup must equal it. A second
nonidentity element of the four-subgroup gives the contradiction.

This is the fixed-involution obstruction in ABG II.4 Lemma 17, article
page 45. The proved weak-closure consequence is used directly; it yields the
same fixed point as the source's odd-core reduction without another quotient
transport. The separate D/QD fusion witness will supply the final exclusion.
-/

namespace ABG
open scoped IsKleinFour

public theorem qGroup_not_all_four_involutions_conjugate
    {H : Type*} [Group H] [Finite H] (hH : IsQGroup H)
    (T : Subgroup H) (hT : IsKleinFour T) :
    ¬ ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : H) (y : H) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsKleinFour T := hT
  have hTtwo : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by simp)
  obtain ⟨S, hTS⟩ := hTtwo.exists_le_sylow
  let Ti := T.subgroupOf (S : Subgroup H)
  let e : Ti ≃* T := Subgroup.subgroupOfEquivOfLe hTS
  have hTi : IsKleinFour Ti :=
    ⟨(Nat.card_congr e.toEquiv).trans hT.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans hT.exponent_two⟩
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (qGroup_four_subgroup_inf_center_ne_bot hH S Ti hTi)
  let x : T := ⟨(t.val : H), t.property.1⟩
  have hx : x ≠ 1 := by
    intro h
    apply ht
    have hv : (x : H) = 1 := congrArg (fun a : T => (a : H)) h
    exact Subtype.ext (Subtype.ext hv)
  have hxC : (x : H) ∈ subgroupCenter (S : Subgroup H) :=
    ⟨t.val, t.property.2, rfl⟩
  have hxorder : orderOf (x : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by simpa only [pow_two] using IsKleinFour.mul_self x) hx
  let : Fintype T := Fintype.ofFinite T
  have hcard : ({1, x} : Finset T).card < (Finset.univ : Finset T).card := by
    rw [Finset.card_univ, IsKleinFour.card_four']
    have hle := Finset.card_insert_le (1 : T) {x}
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hy' : y ≠ 1 ∧ y ≠ x := by simpa using hy
  intro hfuse
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfuse x y hx hy'.1)
  let W := Subgroup.zpowers (x : H)
  have hWC : W ≤ subgroupCenter (S : Subgroup H) := Subgroup.zpowers_le.mpr hxC
  have hweak := hH.hasWeaklyClosedCenterSubgroups S W hWC
  have hgxy : (MulAut.conj g) (x : H) = (y : H) := hg
  have hmap : W.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup H) := by
    change (Subgroup.zpowers (x : H)).map (MulAut.conj g).toMonoidHom ≤ _
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj g) (x : H)) ≤ _
    rw [hgxy]
    exact Subgroup.zpowers_le.mpr (hTS y.property)
  have heq : W.map (MulAut.conj g).toMonoidHom = W := by
    have h := hweak.2 g⁻¹ (by
      change W.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom ≤ (S : Subgroup H)
      simpa only [inv_inv] using hmap)
    change W.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom = W at h
    simpa only [inv_inv] using h
  have hyW : (y : H) ∈ W := by
    rw [← heq]
    exact ⟨x, Subgroup.mem_zpowers (x : H), hgxy⟩
  have hycases : (y : H) = 1 ∨ (y : H) = (x : H) := by
    change (y : H) ∈ Subgroup.zpowers (x : H) at hyW
    rw [mem_zpowers_iff_mem_range_orderOf, hxorder] at hyW
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hyW
    have hn' : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (by simpa using he.symm)
  rcases hycases with hyone | hyx
  · exact hy'.1 (Subtype.ext hyone)
  · exact hy'.2 (Subtype.ext hyx)

end ABG
