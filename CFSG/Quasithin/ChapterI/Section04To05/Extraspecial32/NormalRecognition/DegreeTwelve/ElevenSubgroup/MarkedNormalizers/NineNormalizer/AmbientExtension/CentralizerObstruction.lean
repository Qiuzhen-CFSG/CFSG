module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension.Reduction
public import Theory.GroupTheory.FixedInvertedFactorization
public import Theory.GroupTheory.SemidihedralCenter

/-!
# The order-27 centralizer obstruction

Let D be the literal marked nine-group and b = uz. In the remaining case
B = C_G(D) has order 27 and is abelian. The semidihedral presentation gives
an order-eight rotation p with p⁴ = b. Since B/D has order three, p² acts
trivially on it. Thus b acts trivially on B/D, and fixed/inverted
factorization, together with b inverting D, gives B = D × C_B(b).

The fixed factor has order three and is normalized by p, so p² centralizes
it and has order four. Conjugating b to z and then using Sylow conjugacy
inside C_G(z) carries the fixed cubic to the original X. This contradicts
the order-four obstruction in C_G(X).

Only the explicit involution-fusion premise is retained; the parent supplies
it from the local census. No splitting or ambient recognition is assumed.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.9, p.41.
-/

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

private theorem rotation (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    ∃ p : m.P, orderOf p = 8 ∧ (p : G) ^ 4 = s.u * z := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hgen⟩ := m.semidihedral
  have hclosure : closure ({p, q} : Set m.P) = ⊤ := by
    rw [show ({p, q} : Set m.P) = {p} ∪ {q} by ext; simp [or_comm],
      Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure, hgen]
  have hc : center m.P = zpowers (p ^ 4) :=
    Semidihedral.center_eq (n := 4) (by decide) p q hp hq hpq hclosure
  have hp4 : orderOf (p ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by decide) (by rw [hp]; decide), hp]
  have hm : (p : G) ^ 4 ∈ zpowers (s.u * z) := by
    rw [← m.center_P]
    exact mem_map_of_mem m.P.subtype (hc ▸ mem_zpowers (p ^ 4))
  rw [mem_zpowers_iff_mem_range_orderOf, s.uz_order] at hm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  have hil : i < 2 := Finset.mem_range.mp hi
  refine ⟨p, hp, ?_⟩
  interval_cases i
  · have hne : (p : G) ^ 4 ≠ 1 := by
      intro he
      have he' : p ^ 4 = 1 := Subtype.ext he
      rw [he', orderOf_one] at hp4
      contradiction
    exact False.elim (hne (by simpa using he.symm))
  · simpa using he.symm

private theorem aut_three_sq {T : Type*} [Group T] [Finite T]
    (hc : Nat.card T = 3) (f : MulAut T) : f ^ 2 = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic T := isCyclic_of_prime_card hc
  have hf : Nat.card (MulAut T) = 2 := by rw [IsCyclic.card_mulAut, hc]; decide
  simpa only [hf] using pow_card_eq_one' (x := f)

private theorem fixed_factor (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (hB : Nat.card (centralizer (s.markedNine : Set G)) = 27) :
    s.markedNine ⊔ (centralizer (s.markedNine : Set G) ⊓ Centralizer (s.u * z)) =
      centralizer (s.markedNine : Set G) := by
  let B := centralizer (s.markedNine : Set G)
  let D := s.markedNine.subgroupOf B
  let : IsMulCommutative B := centralizer_abelian_of_card_twenty_seven s hB
  have hDB := markedNine_le_centralizer s
  have hD : Nat.card D = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv, s.card_markedNine]
  have hQ : Nat.card (B ⧸ D) = 3 := by
    have hh := D.card_mul_index
    rw [hD, hB] at hh
    change D.index = 3
    omega
  obtain ⟨p, hp, hp4⟩ := rotation s m
  have hpD := complement_le_normalizer s m p.property
  have hpB := normalizer_le_normalizer_centralizer s.markedNine hpD
  let f : MulAut B := B.normalizerMonoidHom ⟨p, hpB⟩
  have hfD : D.map f.toMonoidHom = D := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨x, hx, rfl⟩
      exact (hpD x).mp hx
    · rw [card_map_of_injective (f := f.toMonoidHom) f.injective]
  let fQ : MulAut (B ⧸ D) := QuotientGroup.congr D D f hfD
  have hfQ : fQ ^ 4 = 1 := by rw [show 4 = 2 * 2 by decide, pow_mul, aut_three_sq hQ]
  have hf4 (x : B) : ((f ^ 4) x : G) = (s.u * z) * x * (s.u * z)⁻¹ := by
    change ((B.normalizerMonoidHom ⟨p, hpB⟩ ^ 4) x : G) = _
    rw [← map_pow]
    change (p : G) ^ 4 * x * ((p : G) ^ 4)⁻¹ = _
    rw [hp4]
  have hfQmk (x : B) : fQ (QuotientGroup.mk' D x) = QuotientGroup.mk' D (f x) := rfl
  have hfQ4 (x : B) : QuotientGroup.mk' D ((f ^ 4) x) = QuotientGroup.mk' D x := by
    have he := DFunLike.congr_fun hfQ (QuotientGroup.mk' D x)
    simpa only [show (4 : ℕ) = 2 + 2 by decide, pow_add, pow_two,
      MulAut.mul_apply, MulAut.one_apply, hfQmk] using he
  let bN : normalizer (B : Set G) := ⟨s.u * z, hp4 ▸ pow_mem hpB 4⟩
  let φ : MulAut B := B.normalizerMonoidHom bN
  have hφ : Function.Involutive φ := by
    intro x
    apply Subtype.ext
    change (s.u * z) * ((s.u * z) * x * (s.u * z)⁻¹) * (s.u * z)⁻¹ = (x : G)
    calc
      _ = (s.u * z) ^ 2 * x * ((s.u * z) ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = x := by rw [s.uz_sq]; simp
  have hinverted (x : B) (hx : φ x = x⁻¹) : (x : G) ∈ s.markedNine := by
    have he : (f ^ 4) x = x⁻¹ := by
      apply Subtype.ext
      rw [hf4]
      exact congrArg Subtype.val hx
    have hi := hfQ4 x
    rw [he, map_inv] at hi
    have h2 : (QuotientGroup.mk' D x) ^ 2 = 1 := by
      rw [pow_two]
      exact inv_eq_iff_mul_eq_one.mp hi
    have h3 : orderOf (QuotientGroup.mk' D x) ∣ 3 := hQ ▸ orderOf_dvd_natCard _
    have he1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
        (orderOf_dvd_of_pow_eq_one h2) h3)
    exact (QuotientGroup.eq_one_iff x).mp he1
  apply le_antisymm
  · exact sup_le hDB inf_le_left
  · intro x hx
    obtain ⟨⟨c, d⟩, ⟨hc, hd, hcd⟩, -⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card
        (show Odd (Nat.card B) by rw [hB]; decide) φ hφ ⟨x, hx⟩
    have hcC : (c : G) ∈ B ⊓ Centralizer (s.u * z) := by
      refine ⟨c.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have he := congrArg Subtype.val hc
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hdm : (d : G) ∈ s.markedNine := hinverted d hd
    have he := congrArg Subtype.val hcd
    change (c : G) * (d : G) = x at he
    rw [← he]
    apply (s.markedNine ⊔ (B ⊓ Centralizer (s.u * z))).mul_mem
    · exact (show B ⊓ Centralizer (s.u * z) ≤ _ from le_sup_right) hcC
    · exact (show s.markedNine ≤ _ from le_sup_left) hdm

private theorem fixed_cubic (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (hB : Nat.card (centralizer (s.markedNine : Set G)) = 27) :
    Nat.card (centralizer (s.markedNine : Set G) ⊓ Centralizer (s.u * z) : Subgroup G) = 3 := by
  let C := centralizer (s.markedNine : Set G) ⊓ Centralizer (s.u * z)
  have hd : Disjoint s.markedNine C :=
    (disjoint_iff.mpr s.markedNine_inf_centralizer_uz).mono_right inf_le_right
  obtain ⟨e, -⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    s.markedNine C hd (le_centralizer_iff.mp inf_le_left)
  have hc := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, s.card_markedNine, fixed_factor s m hB, hB] at hc
  change Nat.card C = 3
  omega

private theorem four_centralizes_fixed_cubic (s : SymmetricSixData h a)
    (m : M10NormalizerGeometry s)
    (hB : Nat.card (centralizer (s.markedNine : Set G)) = 27) :
    ∃ x : G, orderOf x = 4 ∧
      x ∈ centralizer ((centralizer (s.markedNine : Set G) ⊓ Centralizer (s.u * z) : Subgroup G) : Set G) := by
  let C := centralizer (s.markedNine : Set G) ⊓ Centralizer (s.u * z)
  obtain ⟨p, hp, hp4⟩ := rotation s m
  have hpB := normalizer_le_normalizer_centralizer s.markedNine
    (complement_le_normalizer s m p.property)
  have hpCb : (p : G) ∈ Centralizer (s.u * z) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hp4]
    exact (Commute.self_pow (p : G) 4).eq
  have hpC : (p : G) ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hpB, (Centralizer (s.u * z)).le_normalizer hpCb⟩
  let f : MulAut C := C.normalizerMonoidHom ⟨p, hpC⟩
  have hf := aut_three_sq (fixed_cubic s m hB) f
  refine ⟨(p : G) ^ 2, ?_, ?_⟩
  · have ho : orderOf (p : G) = 8 := (orderOf_coe p).trans hp
    rw [orderOf_pow_of_dvd (by decide) (by rw [ho]; decide), ho]
  · intro c hc
    have he := congrArg (fun k : MulAut C => (k ⟨c, hc⟩ : G)) hf
    change (p : G) * ((p : G) * c * (p : G)⁻¹) * (p : G)⁻¹ = c at he
    have he' : (p : G) ^ 2 * c * ((p : G) ^ 2)⁻¹ = c := by
      simpa only [pow_two, mul_inv_rev, mul_assoc] using he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm

private theorem cubic_conjugation (_s : SymmetricSixData h a) {b : G}
    (hb : IsConj z b) (Y : Subgroup G) (hY : Y ≤ Centralizer b)
    (hc : Nat.card Y = 3) :
    ∃ e : MulAut G, e b = z ∧ Y.map e.toMonoidHom = cubicInG h := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hb.symm
  let e := MulAut.conj g
  let Yg := Y.map e.toMonoidHom
  have hYg : Yg ≤ Centralizer z := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he : e b = z := hg
    rw [← he]
    change e x * e b = e b * e x
    rw [← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp (hY hx))
  have hcg : Nat.card Yg = 3 := by
    rw [card_map_of_injective (f := e.toMonoidHom) e.injective, hc]
  let T : Sylow 3 (Centralizer z) := Sylow.ofCard (Yg.subgroupOf (Centralizer z)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYg).toEquiv, hcg, h.centralizer_card]
    decide +kernel)
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Centralizer z) T h.X
  have ht' : (T : Subgroup (Centralizer z)).map (MulAut.conj t).toMonoidHom = h.X :=
    congrArg Sylow.toSubgroup ht
  have hTmap : (T : Subgroup (Centralizer z)).map (Centralizer z).subtype = Yg :=
    map_subgroupOf_eq_of_le hYg
  have hmap : Yg.map (MulAut.conj (t : G)).toMonoidHom = cubicInG h := by
    rw [← hTmap]
    calc
      _ = ((T : Subgroup (Centralizer z)).map (MulAut.conj t).toMonoidHom).map
          (Centralizer z).subtype := by rw [map_map, map_map]; rfl
      _ = cubicInG h := by rw [ht']; rfl
  refine ⟨e.trans (MulAut.conj (t : G)), ?_, ?_⟩
  · change (t : G) * (g * b * g⁻¹) * (t : G)⁻¹ = z
    rw [hg]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property)
  change (Y.map e.toMonoidHom).map (MulAut.conj (t : G)).toMonoidHom = _ at hmap
  rw [map_map] at hmap
  exact hmap

private theorem cubic_no_order_four (s : SymmetricSixData h a) {b : G}
    (hb : IsConj z b) (Y : Subgroup G) (hY : Y ≤ Centralizer b)
    (hc : Nat.card Y = 3) (x : G) (hx : x ∈ centralizer (Y : Set G)) :
    orderOf x ≠ 4 := by
  obtain ⟨e, -, he⟩ := cubic_conjugation s hb Y hY hc
  have hxe : e x ∈ centralizer (cubicInG h : Set G) := by
    rw [← he]
    rintro _ ⟨y, hy, rfl⟩
    change e y * e x = e x * e y
    simpa only [map_mul] using congrArg e (hx y hy)
  simpa only [e.orderOf_eq] using centralizer_X_no_order_four s (e x) hxe

/-- The order-27 alternative is impossible when the marked involution `uz`
is conjugate to `z`. The fusion premise is discharged by the census in the
parent ambient-extension assembly. -/
public theorem centralizer_markedNine_eq_of_isConj (s : SymmetricSixData h a)
    (m : M10NormalizerGeometry s) (hb : IsConj z (s.u * z)) :
    centralizer (s.markedNine : Set G) = s.markedNine := by
  rcases centralizer_card_cases s m with hB | hB
  · exact (eq_of_le_of_card_ge (markedNine_le_centralizer s)
      (by rw [hB, s.card_markedNine])).symm
  · obtain ⟨x, hx4, hx⟩ := four_centralizes_fixed_cubic s m hB
    exact False.elim (cubic_no_order_four s hb _ inf_le_right
      (fixed_cubic s m hB) x hx hx4)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
