module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.FixedInvolution
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ComplementAction

/-!
# The conjugate centralizer of Bender's plane

For an order-three subgroup `X` fixing an involution, involution fusion
moves `X` into the distinguished centralizer of order 120. Sylow conjugacy
inside that centralizer gives an actual ambient conjugation carrying
`⟨x⟩` to `X`. It carries the odd complement `A` to a subgroup `B` whose
members are exactly the odd-order elements of `C_G(X)`.

The literal plane `Y = (A ⊓ C_G(X)) ⊔ X` centralizes `X`. Its supplied
order nine therefore puts it in `B`. No involution can centralize `Y`,
since every involution centralizer has order 120. Thus `C_G(Y)` has odd
order and is also contained in `B`. The elementary abelian structure of
`B` supplies the reverse containment.

This proves the conditional conjugate-centralizer producer in
`not_exceptionalOddNormalizer_of_local_steps`. The fixed involution and
plane cardinality remain explicit inputs, supplied by the parent assembly;
no ambient Sylow-three order or structural-alternatives producer is used.

Source: Bender, *Finite groups with large subgroups* (1974), proof of
(4.1), printed p.225, the step `Y ≤ B` and `B = C_G(Y)`.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem cubic_conjugate (h : Janko1CentralizerData G)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    (X : Subgroup G) (hX : Nat.card X = 3)
    (ht : ∃ t : G, orderOf t = 2 ∧ X ≤ centralizer ({t} : Set G)) :
    ∃ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom = X := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t, ht, hXt⟩ := ht
  obtain ⟨s, hs⟩ := h.involutions_conjugate t ht
  let f := MulAut.conj s
  let C := centralizer ({h.z} : Set G)
  let X' := X.map f.toMonoidHom
  have hX'C : X' ≤ C := by
    rintro w ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change f v * h.z = h.z * f v
    rw [← show f t = h.z from hs, ← map_mul, ← map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp (hXt hv))
  have hUC : zpowers x ≤ C := zpowers_le.mpr hxC
  have sylow_of_three (D : Subgroup G) (hDC : D ≤ C) (hD : Nat.card D = 3) :
      ∃ P : Sylow 3 C, (P : Subgroup C) = D.subgroupOf C := by
    have hc : Nat.card (D.subgroupOf C) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hD
    have hi := (D.subgroupOf C).card_mul_index
    rw [hc, show Nat.card C = 120 from h.centralizer_card] at hi
    have hidx : (D.subgroupOf C).index = 40 := by omega
    have hpD : IsPGroup 3 (D.subgroupOf C) :=
      IsPGroup.of_card (n := 1) (by simpa using hc)
    exact ⟨hpD.toSylow (by rw [hidx]; decide), rfl⟩
  obtain ⟨P, hP⟩ := sylow_of_three X' hX'C (by
    rw [card_map_of_injective f.injective, hX])
  obtain ⟨Q, hQ⟩ := sylow_of_three (zpowers x) hUC (by rw [Nat.card_zpowers, hx])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq C P Q
  have hmap : X.map (MulAut.conj ((n : G) * s)).toMonoidHom = zpowers x := by
    apply eq_of_le_of_card_ge
    · rintro w ⟨v, hv, rfl⟩
      have hv' : f v ∈ X' := mem_map.mpr ⟨v, hv, rfl⟩
      let vC : C := ⟨f v, hX'C hv'⟩
      have hvP : vC ∈ (P : Subgroup C) := by rw [hP]; exact hv'
      have hnQ : n * vC * n⁻¹ ∈ (Q : Subgroup C) := by
        rw [← hn]
        exact ⟨vC, hvP, rfl⟩
      rw [hQ] at hnQ
      change (n : G) * (s * v * s⁻¹) * (n : G)⁻¹ ∈ zpowers x at hnQ
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, mul_inv_rev, mul_assoc] using hnQ
    · rw [card_map_of_injective (MulAut.conj _).injective, hX, Nat.card_zpowers, hx]
  refine ⟨((n : G) * s)⁻¹, ?_⟩
  rw [← hmap, map_map]
  have he : (MulAut.conj ((n : G) * s)⁻¹).toMonoidHom.comp
      (MulAut.conj ((n : G) * s)).toMonoidHom = MonoidHom.id G := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

omit [Finite G] [IsSimpleGroup G] in
private theorem map_centralizer (D : Subgroup G) (f : G ≃* G) :
    (centralizer (D : Set G)).map f.toMonoidHom =
      centralizer (D.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro y hy
    rw [mem_map_equiv]
    intro d hd
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hy (f d) (mem_map.mpr ⟨d, hd, rfl⟩)

omit [IsSimpleGroup G] in
private theorem odd_le_conjugate (h : Janko1CentralizerData G)
    {x : G} {A : Subgroup G} (a : OddCentralizerComplement h x A)
    (f : G ≃* G) (X : Subgroup G) (hf : (zpowers x).map f.toMonoidHom = X)
    (D : Subgroup G) (hD : Odd (Nat.card D)) (hDC : D ≤ centralizer (X : Set G)) :
    D ≤ A.map f.toMonoidHom := by
  have hC : (centralizer ({x} : Set G)).map f.toMonoidHom = centralizer (X : Set G) := by
    rw [← hf, ← map_centralizer, zpowers_eq_closure, centralizer_closure]
  intro y hy
  rw [mem_map_equiv]
  apply (a.mem_iff_odd_orderOf ?_).mpr
  · rw [f.symm.orderOf_eq]
    have ho := hD.of_dvd_nat (orderOf_dvd_natCard (⟨y, hy⟩ : D))
    rwa [← orderOf_injective D.subtype Subtype.val_injective] at ho
  · have hc := hDC hy
    rw [← hC, mem_map_equiv] at hc
    exact hc

/-- Bender's actual conjugate `B` of the odd complement is the ambient
centralizer of `Y`, and contains `Y`. The two explicit local inputs are
precisely those passed to the conjugate-centralizer producer by the
exceptional-exclusion assembly. -/
public theorem exceptional_conjugate_centralizer (h : Janko1CentralizerData G)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (e : ExceptionalOddNormalizer A) (X : Subgroup G) (hX : Nat.card X = 3)
    (ht : ∃ t : G, orderOf t = 2 ∧ X ≤ centralizer ({t} : Set G))
    (hY : Nat.card (exceptionalPlane A X) = 9) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom =
      centralizer (exceptionalPlane A X : Set G) ∧
      exceptionalPlane A X ≤ A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := cubic_conjugate h x hxC hx X hX ht
  let f := MulAut.conj g
  let B := A.map f.toMonoidHom
  let Y := exceptionalPlane A X
  have hXY : X ≤ Y := le_sup_right
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : IsCyclic X := isCyclic_of_prime_card hX
  have hYC : Y ≤ centralizer (X : Set G) := sup_le inf_le_right (le_centralizer X)
  have hYodd : Odd (Nat.card Y) := by rw [show Nat.card Y = 9 from hY]; decide
  have hYB : Y ≤ B := odd_le_conjugate h a f X hg Y hYodd hYC
  have hCodd : Odd (Nat.card (centralizer (Y : Set G))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro hd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (Y : Set G)) 2 hd
    have ht' : orderOf (t : G) = 2 :=
      (orderOf_injective (centralizer (Y : Set G)).subtype Subtype.val_injective t).trans ht
    have hYt : Y ≤ centralizer ({(t : G)} : Set G) := by
      intro y hy
      rw [mem_centralizer_singleton_iff]
      exact t.property y hy
    have hd9 := card_dvd_of_le hYt
    rw [show Nat.card Y = 9 from hY, h.involution_centralizer_card _ ht'] at hd9
    norm_num at hd9
  have hCB : centralizer (Y : Set G) ≤ B :=
    odd_le_conjugate h a f X hg _ hCodd (centralizer_le hXY)
  have hBC : B ≤ centralizer (Y : Set G) := by
    let _ := (e.map f).elementary
    exact (le_centralizer B).trans (centralizer_le hYB)
  exact ⟨g, le_antisymm hBC hCB, hYB⟩
end CFSG.Quasithin.Janko1CentralizerData
