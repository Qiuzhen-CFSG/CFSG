module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.RootPairs.AlternatingFive
/-!
# The root-involution pair count a(t) = 195

A marked equivalence C_G(t) ≃ E₄ × A₅ suffices for this count. Since t is
central in its centralizer and A₅ has trivial center, t has coordinates
(w,1), with w nonidentity. The fusion marking puts the first member of a
source pair at (1,a). Literal membership t ∈ ⟨uv⟩ forces the second member
to have coordinates (w,x), with ax of odd order. Conversely these conditions
produce precisely a source pair, using the two ambient involution classes.

The resulting bijection transports the kernel-checked A₅ count. Its domain
allows x = 1; `RootPairs.second_ne_one` explains why this case contributes
nothing. No selected geometry, normalizer model, or ambient order is used.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.260.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

private theorem four_square (b : E4) : b ^ 2 = 1 := by
  have h : ∀ b : E4, b ^ 2 = 1 := by decide +kernel
  exact h b

private theorem pow_of_square {H : Type*} [Monoid H] (b : H) (hb : b ^ 2 = 1)
    (n : ℕ) : b ^ n = b ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, hb, one_pow, mul_one]

private theorem root_mem_zpowers {w b : E4} (hw : w ≠ 1) (y : A5) :
    (w, 1) ∈ zpowers (b, y) ↔ b = w ∧ Odd (orderOf y) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr h)
    have hb : b ^ n = w := congrArg Prod.fst hn
    have hy : y ^ n = 1 := congrArg Prod.snd hn
    have hnodd : Odd n := Nat.odd_iff.mpr (by
      have hh := Nat.mod_lt n (by decide : 0 < 2)
      have hn0 : n % 2 ≠ 0 := by
        intro he
        rw [pow_of_square b (four_square b), he, pow_zero] at hb
        exact hw hb.symm
      omega)
    have hbw : b = w := by
      rwa [pow_of_square b (four_square b), Nat.odd_iff.mp hnodd, pow_one] at hb
    exact ⟨hbw, hnodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hy)⟩
  · rintro ⟨hbw, ho⟩
    subst b
    have hh : (w, y) ^ orderOf y = (w, 1) := by
      apply Prod.ext
      · exact (pow_of_square w (four_square w) _).trans
          (by rw [Nat.odd_iff.mp ho, pow_one])
      · exact pow_orderOf_eq_one y
    exact hh ▸ npow_mem_zpowers (w, y) (orderOf y)

variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

private def centralT (t : G) : involutionCentralizer t :=
  ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩

private theorem coordinates_t (C : SecondCentralizer D t) :
    (C.equiv (centralT t)).2 = 1 := by
  have hc : centralT t ∈ center (involutionCentralizer t) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp g.property
  have hh := (centerCongr C.equiv ⟨centralT t, hc⟩).property
  change C.equiv (centralT t) ∈ center (E4 × A5) at hh
  rw [Subgroup.center_prod] at hh
  have h2 : (C.equiv (centralT t)).2 ∈ center A5 := hh.2
  rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)), mem_bot] at h2
  exact h2

private theorem coordinates_t_ne (ht : OtherInvolution D t) (C : SecondCentralizer D t) :
    (C.equiv (centralT t)).1 ≠ 1 := by
  intro he
  exact ht.2 ((C.fusion (centralT t) ((orderOf_coe _).symm.trans ht.1)).mpr he)

private theorem embedding_t (C : SecondCentralizer D t) :
    C.embedding ((C.equiv (centralT t)).1, 1) = t := by
  have hh : ((C.equiv (centralT t)).1, 1) = C.equiv (centralT t) := by
    apply Prod.ext
    · rfl
    · exact (coordinates_t C).symm
  rw [hh]
  simp [SecondCentralizer.embedding, centralT]

private theorem embedding_order (C : SecondCentralizer D t) (x : E4 × A5) :
    orderOf (C.embedding x) = orderOf x :=
  orderOf_injective C.embedding C.embedding_injective x

private theorem embedding_fusion (C : SecondCentralizer D t) (x : E4 × A5)
    (hx : orderOf x = 2) : IsConj D.z (C.embedding x) ↔ x.1 = 1 := by
  simpa [SecondCentralizer.embedding] using
    C.fusion (C.equiv.symm x) ((C.equiv.symm.orderOf_eq x).trans hx)

private theorem embedding_zpowers (C : SecondCentralizer D t) (a b : E4 × A5) :
    C.embedding a ∈ zpowers (C.embedding b) ↔ a ∈ zpowers b := by
  simp only [mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, C.embedding_injective (by simpa only [map_zpow] using hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← map_zpow, hn]⟩

omit [Finite G] in
private theorem conjugate_order {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

private theorem first_order (a : A5) (ha : a ^ 2 = 1 ∧ a ≠ 1) :
    orderOf ((1, a) : E4 × A5) = 2 := by
  apply orderOf_eq_prime
  · apply Prod.ext <;> simp [ha.1]
  · intro h
    exact ha.2 (congrArg Prod.snd h)

private theorem second_order (w : E4) (hw : w ≠ 1) (x : A5) (hx : x ^ 2 = 1) :
    orderOf (w, x) = 2 := by
  apply orderOf_eq_prime
  · apply Prod.ext
    · exact four_square w
    · exact hx
  · intro h
    exact hw (congrArg Prod.fst h)

private def pairToSource (ht : OtherInvolution D t) (C : SecondCentralizer D t)
    (p : RootPairs.OddPairs) : SourcePairs D.z t t := by
  let w := (C.equiv (centralT t)).1
  have hw : w ≠ 1 := coordinates_t_ne ht C
  have hu := first_order p.val.1.val p.val.1.property
  have hv := second_order w hw p.val.2.val p.val.2.property
  refine ⟨(C.embedding (1, p.val.1.val), C.embedding (w, p.val.2.val)), ?_, ?_, ?_⟩
  · exact (embedding_fusion C _ hu).mpr rfl
  · apply (ht.classes _ ((embedding_order C _).trans hv)).resolve_left
    intro h
    exact hw ((embedding_fusion C _ hv).mp h)
  · have hm : C.embedding (w, 1) ∈
        zpowers (C.embedding ((1, p.val.1.val) * (w, p.val.2.val))) := by
      apply (embedding_zpowers C _ _).mpr
      simpa only [Prod.mul_def, one_mul] using
        (root_mem_zpowers hw (p.val.1.val * p.val.2.val)).mpr ⟨rfl, p.property⟩
    simpa only [w, map_mul, embedding_t] using hm

private theorem pairToSource_injective (ht : OtherInvolution D t)
    (C : SecondCentralizer D t) : Function.Injective (pairToSource ht C) := by
  intro p q h
  have h1 := congrArg (fun r : SourcePairs D.z t t => r.val.1) h
  have h2 := congrArg (fun r : SourcePairs D.z t t => r.val.2) h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.snd (C.embedding_injective h1)
  · exact congrArg Prod.snd (C.embedding_injective h2)

private theorem pairToSource_surjective (ht : OtherInvolution D t)
    (C : SecondCentralizer D t) : Function.Surjective (pairToSource ht C) := by
  intro p
  obtain ⟨hp1, hp2⟩ := sourcePairs_mem_centralizer ht ht.1 p
  let a := C.equiv ⟨p.val.1, hp1⟩
  let b := C.equiv ⟨p.val.2, hp2⟩
  let w := (C.equiv (centralT t)).1
  have ha : C.embedding a = p.val.1 := by simp [a, SecondCentralizer.embedding]
  have hb : C.embedding b = p.val.2 := by simp [b, SecondCentralizer.embedding]
  have hao : orderOf a = 2 := by
    rw [← embedding_order C a, ha]
    exact (conjugate_order p.property.1).symm.trans D.localType.involution
  have hbo : orderOf b = 2 := by
    rw [← embedding_order C b, hb]
    exact (conjugate_order p.property.2.1).symm.trans ht.1
  have ha1 : a.1 = 1 := (embedding_fusion C a hao).mp (ha.symm ▸ p.property.1)
  have ha2 : a.2 ^ 2 = 1 := congrArg Prod.snd (orderOf_eq_prime_iff.mp hao).1
  have ha2ne : a.2 ≠ 1 := by
    intro h
    exact (orderOf_eq_prime_iff.mp hao).2 (Prod.ext ha1 h)
  have hb2 : b.2 ^ 2 = 1 := congrArg Prod.snd (orderOf_eq_prime_iff.mp hbo).1
  have hmem : (w, 1) ∈ zpowers (a * b) := by
    apply (embedding_zpowers C _ _).mp
    rw [map_mul, ha, hb]
    exact (embedding_t C).symm ▸ p.property.2.2
  have hroot : b.1 = w ∧ Odd (orderOf (a.2 * b.2)) := by
    apply (root_mem_zpowers (coordinates_t_ne ht C) _).mp
    simpa only [Prod.mul_def, ha1, one_mul] using hmem
  let q : RootPairs.OddPairs := ⟨(⟨a.2, ha2, ha2ne⟩, ⟨b.2, hb2⟩), hroot.2⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change C.embedding (1, a.2) = p.val.1
    rw [show (1, a.2) = a from Prod.ext ha1.symm rfl, ha]
  · change C.embedding (w, b.2) = p.val.2
    rw [show (w, b.2) = b from Prod.ext hroot.1.symm rfl, hb]

/-- The literal source pairs are in bijection with the odd-product pairs in A₅. -/
noncomputable def SecondCentralizer.sourcePairsEquivOddPairs
    (C : SecondCentralizer D t) (ht : OtherInvolution D t) :
    SourcePairs D.z t t ≃ RootPairs.OddPairs :=
  (Equiv.ofBijective (pairToSource ht C)
    ⟨pairToSource_injective ht C, pairToSource_surjective ht C⟩).symm

/-- The conditional root-involution count in 47.1, using only the marked centralizer. -/
theorem SecondCentralizer.sourceCount_eq_195 (C : SecondCentralizer D t)
    (ht : OtherInvolution D t) : sourceCount D.z t t = 195 := by
  rw [sourceCount, Nat.card_congr (C.sourcePairsEquivOddPairs ht), RootPairs.card_pairs]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
