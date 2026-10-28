module

public import Theory.GroupTheory.QuaternionCentralProductAutomorphisms
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Linarith

/-!
# A central-square element outside a quaternion central product

Let a group of order 256 be a two-group, and let two commuting quaternion
subgroups generate a normal self-centralizing subgroup, with intersection of
order two. There is an element outside their join which centralizes the first
factor and whose square lies in the intersection.

The intrinsic quaternion factors give the first factor's normalizer index at
most two. Its conjugation image has order dividing eight, since Aut(Q8) has
order 24. Thus the factor centralizer has at least sixteen elements, whereas
its intersection with the join is just the other quaternion factor. Choose an
outside centralizer element. A kernel-checked quaternion calculation shows
that an automorphism whose eighth power is one can be multiplied by an inner
automorphism to have square one. Multiplying the chosen element by the
corresponding element of the second factor gives the desired element. Its
square centralizes both factors; self-centralization and the factor-center
calculation place that square in the shared intersection.

This is the intrinsic centralizer-element selection for Janko–Thompson,
Math. Z. 113 (1970), §4, case (c), printed p.392, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
It needs neither a fusion hypothesis nor an elementary-rank bound. The later
correction to an actual involution is in QuaternionCentralProductInvolutionCorrection.
-/

open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem normalizer_index (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [(B ⊔ C).Normal] : (normalizer (B : Set G)).index ≤ 2 := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  have heq : normalizer (B : Set G) = MulAction.stabilizer G B := by
    ext g
    exact mem_normalizer_iff_map_conj_eq
  rw [heq, MulAction.index_stabilizer]
  have himage (g : G) : B.map (MulAut.conj g).toMonoidHom = B ∨
      B.map (MulAut.conj g).toMonoidHom = C := by
    obtain ⟨eB⟩ := hB
    apply quaternion_subgroup_eq_factor B C _ ⟨eB⟩ hC hinter hcomm
    · exact ⟨((MulAut.conj g).subgroupMap B).symm.trans eB⟩
    · exact (map_mono (show B ≤ B ⊔ C from le_sup_left)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial))
  have hsubset : MulAction.orbit G B ⊆ {B, C} := by
    rintro D ⟨g, rfl⟩
    exact himage g
  exact (Set.ncard_le_ncard hsubset).trans (by by_cases h : B = C <;> simp [h])

private theorem aut_range_card_dvd_eight {A D : Type*} [Group A] [Finite A]
    [Group D] [Finite D] (hA : IsPGroup 2 A) (e : D ≃* QuaternionGroup 2)
    (f : A →* MulAut D) : Nat.card f.range ∣ 8 := by
  have hcard : Nat.card (MulAut D) = 24 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans QuaternionGroup.card_mulAut_two
  have hd := f.range.card_subgroup_dvd_card
  rw [hcard] at hd
  obtain ⟨n, hn⟩ := (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra h
    have hh : 16 ∣ 24 := (show 2^4 ∣ 2^n from pow_dvd_pow 2 (by omega)).trans (hn ▸ hd)
    norm_num at hh
  rw [hn]
  exact pow_dvd_pow 2 hnle

private theorem centralizer_card_ge (hG : IsPGroup 2 G) (hcard : Nat.card G = 256)
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [(B ⊔ C).Normal] : 16 ≤ Nat.card (centralizer (B : Set G)) := by
  have hindex := normalizer_index B C hB hC hinter hcomm
  have hncount := (normalizer (B : Set G)).card_mul_index
  rw [hcard] at hncount
  have hncard : 128 ≤ Nat.card (normalizer (B : Set G)) := by nlinarith
  obtain ⟨eB⟩ := hB
  let f := B.normalizerMonoidHom
  have hrange := aut_range_card_dvd_eight (hG.to_subgroup _) eB f
  have hrle : Nat.card f.range ≤ 8 := Nat.le_of_dvd (by decide) hrange
  have hk : Nat.card f.ker = Nat.card (centralizer (B : Set G)) := by
    rw [normalizerMonoidHom_ker]
    exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv
  have hcount := f.ker.card_mul_index
  rw [index_ker, hk] at hcount
  nlinarith

private theorem join_inf_centralizer (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    (B ⊔ C) ⊓ centralizer (B : Set G) = C := by
  apply le_antisymm
  · intro x hx
    have hn : B ≤ normalizer (C : Set G) := by
      apply le_trans ?_ (centralizer_le_normalizer _)
      exact fun b hb c hc => (hcomm b hb c hc).symm
    have hx' : x ∈ (↑(B ⊔ C) : Set G) := hx.1
    rw [coe_mul_of_left_le_normalizer_right B C hn] at hx'
    obtain ⟨b, hb, c, hc, rfl⟩ := hx'
    have hbZ : (⟨b, hb⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply mul_right_cancel (b := c)
      calc
        (y : G) * b * c = (y : G) * (b*c) := mul_assoc _ _ _
        _ = (b*c) * y := hx.2 y y.property
        _ = b * y * c := by rw [mul_assoc, ← hcomm y y.property c hc, ← mul_assoc]
    have hbC : b ∈ B ⊓ C := by
      rw [intersection_eq_factor_center B C hB hinter hcomm]
      exact ⟨⟨b,hb⟩, hbZ, rfl⟩
    exact C.mul_mem hbC.2 hc
  · exact fun c hc => ⟨mem_sup_right hc, fun b hb => hcomm b hb c hc⟩

private theorem centralizer_join_le_inter (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hself : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C) :
    centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊓ C := by
  intro x hx
  have hxB : x ∈ centralizer (B : Set G) := fun b hb => hx b (mem_sup_left hb)
  have hxC : x ∈ centralizer (C : Set G) := fun c hc => hx c (mem_sup_right hc)
  constructor
  · have hh : x ∈ (C ⊔ B) ⊓ centralizer (C : Set G) :=
      ⟨by simpa [sup_comm] using hself hx, hxC⟩
    rwa [join_inf_centralizer C B hC (by simpa [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm)] at hh
  · have hh : x ∈ (B ⊔ C) ⊓ centralizer (B : Set G) := ⟨hself hx, hxB⟩
    rwa [join_inf_centralizer B C hB hinter hcomm] at hh

end Subgroup

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def correctionMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem correction_table : ∀ p : Q × Q,
    (∀ x y : Q, correctionMap p (x*y) = correctionMap p x * correctionMap p y) →
    (∀ x : Q, (correctionMap p)^[8] x = x) →
    ∃ z : Q, ∀ x : Q,
      z * correctionMap p (z * correctionMap p x * z⁻¹) * z⁻¹ = x := by
  decide

private theorem correction (e : MulAut Q) (he : e^8 = 1) :
    ∃ z : Q, (MulAut.conj z * e)^2 = 1 := by
  let p : Q × Q := (e (a 1), e (xa 0))
  have hp (x : Q) : correctionMap p x = e x := by
    cases x with
    | a i =>
      change (e (a 1))^i.val = e (a i)
      rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change e (xa 0) * (e (a 1))^i.val = e (xa i)
      rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
  have hm : ∀ x y : Q, correctionMap p (x*y) = correctionMap p x * correctionMap p y := by
    simp only [hp, map_mul, implies_true]
  have hi : ∀ x : Q, (correctionMap p)^[8] x = x := by
    intro x
    have hf : correctionMap p = (e : Q → Q) := funext hp
    rw [hf]
    simpa [pow_succ, Function.iterate_succ_apply] using DFunLike.congr_fun he x
  obtain ⟨z, hz⟩ := correction_table p hm hi
  refine ⟨z, ?_⟩
  ext x
  simpa only [pow_two, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply, hp] using hz x

private theorem correction_of_equiv {D : Type*} [Group D]
    (model : D ≃* Q) (e : MulAut D) (he : e^8 = 1) :
    ∃ z : D, (MulAut.conj z * e)^2 = 1 := by
  have ha : (MulAut.congr model e)^8 = 1 := by rw [← map_pow, he, map_one]
  obtain ⟨z, hz⟩ := correction (MulAut.congr model e) ha
  refine ⟨model.symm z, ?_⟩
  ext x
  apply model.injective
  have hh := DFunLike.congr_fun hz (model x)
  simpa [pow_two, MulAut.congr_apply, MulAut.conj_apply] using hh
end QuaternionGroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- In an order-256 two-group, a normal self-centralizing quaternion central
product admits an outside element centralizing the first factor and squaring
into the shared center. -/
public theorem exists_centralizing_square_of_quaternion_central_product
    (hG : IsPGroup 2 G) (hcard : Nat.card G = 256)
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hNormal : (B ⊔ C).Normal) (_hjoincard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (hself : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C) :
    ∃ k : G, k ∉ B ⊔ C ∧
      k ∈ normalizer ((B ⊔ C : Subgroup G) : Set G) ∧
      k ∈ centralizer (B : Set G) ∧ k^2 ∈ B ⊓ C := by
  let := hNormal
  have hsize := centralizer_card_ge hG hcard B C hB hC hinter hcomm
  have hCcard : Nat.card C = 8 := by
    obtain ⟨eC⟩ := hC
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, hkB, hkout⟩ : ∃ k : G, k ∈ centralizer (B : Set G) ∧ k ∉ B ⊔ C := by
    by_contra! h
    have hle : centralizer (B : Set G) ≤ C := by
      intro k hk
      rw [← join_inf_centralizer B C hB hinter hcomm]
      exact ⟨h k hk, hk⟩
    have hh := card_le_of_le hle
    omega
  have hkN : k ∈ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
    rw [normalizer_eq_top]; trivial
  have hkNC : k ∈ normalizer (C : Set G) := by
    let e := MulAut.conj k
    have hne : B ≠ C := by
      intro heq
      rw [heq, inf_idem, hCcard] at hinter
      omega
    have hBB := mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hkB)
    have hjoin := mem_normalizer_iff_map_conj_eq.mp hkN
    obtain ⟨eC⟩ := hC
    have hfactor := quaternion_subgroup_eq_factor B C (C.map e.toMonoidHom)
      hB ⟨eC⟩ hinter hcomm ⟨(e.subgroupMap C).symm.trans eC⟩
      ((map_mono (show C ≤ B ⊔ C from le_sup_right)).trans_eq hjoin)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases hfactor with h | h
    · exact (hne (map_injective e.injective (hBB.trans h.symm))).elim
    · exact h
  let kk : normalizer (C : Set G) := ⟨k, hkNC⟩
  let f := C.normalizerMonoidHom
  obtain ⟨eC⟩ := hC
  have hd := aut_range_card_dvd_eight (hG.to_subgroup _) eC f
  have he : (f kk)^8 = 1 := by
    have hh : (f.rangeRestrict kk)^8 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hd)
    exact congrArg Subtype.val hh
  obtain ⟨c, hc⟩ := QuaternionGroup.correction_of_equiv eC (f kk) he
  let l : G := (c : G) * k
  have hlB : l ∈ centralizer (B : Set G) :=
    (centralizer (B : Set G)).mul_mem (fun b hb => hcomm b hb c c.property) hkB
  have hlC : l^2 ∈ centralizer (C : Set G) := by
    intro x hx
    have hh := congrArg (fun a : MulAut C => (a ⟨x,hx⟩ : G)) hc
    change (c : G) * (k * ((c : G) * (k * x * k⁻¹) * (c : G)⁻¹) * k⁻¹) *
      (c : G)⁻¹ = x at hh
    have hs : l^2 * x * (l^2)⁻¹ = x := by
      calc
        l^2 * x * (l^2)⁻¹ =
          (c : G) * (k * ((c : G) * (k * x * k⁻¹) * (c : G)⁻¹) * k⁻¹) *
            (c : G)⁻¹ := by dsimp [l]; simp only [pow_two]; group
        _ = x := hh
    exact (mul_inv_eq_iff_eq_mul.mp hs).symm
  have hlZ : l^2 ∈ centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    have hlB2 := (centralizer (B : Set G)).pow_mem hlB 2
    have hle : B ⊔ C ≤ centralizer ({l^2} : Set G) :=
      sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (hlB2 b hb))
        (fun c hc => mem_centralizer_singleton_iff.mpr (hlC c hc))
    exact fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  refine ⟨l, ?_, ?_, hlB, centralizer_join_le_inter B C hB ⟨eC⟩ hinter hcomm hself hlZ⟩
  · intro hl
    exact hkout ((B ⊔ C).mul_mem_cancel_left (mem_sup_right c.property) |>.mp hl)
  · rw [normalizer_eq_top]; trivial
end Subgroup
