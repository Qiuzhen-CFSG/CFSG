module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# The intrinsic quaternion factors of a quaternion central product

Let B and C be commuting quaternion subgroups whose intersection has order two.
Every quaternion subgroup of B ⊔ C equals B or C. Consequently, an automorphism
preserving their join permutes these two factors. Its square preserves each
factor; if its cube is the identity, the automorphism itself preserves each.

In a quaternion group each element is either in its order-two center or has
square equal to the unique involution. The factors share that involution.
Writing an element of the join as b*c shows that a product with both factors
noncentral has square one. Thus every element of order four belongs to one
factor. The two noncommuting standard generators of a quaternion subgroup must
belong to the same factor, and their normal forms prove containment. Equal
orders give equality. The cube-identity corollary excludes the transposition
of the two intrinsic factors. Squaring any permutation of the pair fixes
both factors, yielding the square-invariance companion.

These elementary calculations support the residual action in Stellmacher
(9.1), Journal of Algebra 190 (1997), p.48. They concern actual subgroups and
automorphisms and do not assert fixedfreeness of an arbitrary order-three
automorphism of their central product.
-/

namespace Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem quaternion_square_dichotomy (B : Subgroup G)
    (e : B ≃* QuaternionGroup 2) (z : G) (hz : z ∈ B)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (b : G) (hb : b ∈ B) :
    (b = 1 ∨ b = z) ∨ b ^ 2 = z := by
  have hfinite : ∀ z b : QuaternionGroup 2, z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z := by decide
  let zz : B := ⟨z, hz⟩
  let bb : B := ⟨b, hb⟩
  have hz1' : e zz ≠ 1 := by
    intro hh
    apply hz1
    exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
  have hz2' : (e zz) ^ 2 = 1 := by
    rw [← map_pow]
    have hh : zz ^ 2 = 1 := Subtype.ext hz2
    rw [hh, map_one]
  rcases hfinite (e zz) (e bb) hz1' hz2' with (hb1 | hbz) | hb2
  · exact Or.inl (Or.inl (congrArg Subtype.val
      (e.injective (hb1.trans e.map_one.symm))))
  · exact Or.inl (Or.inr (congrArg Subtype.val (e.injective hbz)))
  · apply Or.inr
    have hh : bb ^ 2 = zz := e.injective (by rw [map_pow]; exact hb2)
    exact congrArg Subtype.val hh

omit [Finite G] in
private theorem order_four_mem_factor (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) (hx : x ∈ B ⊔ C) (hx4 : orderOf x = 4) : x ∈ B ∨ x ∈ C := by
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := hC
  obtain ⟨zz, hz1, _⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  let z : G := zz
  have hz1' : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hz2 : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := zz)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hx' : x ∈ (↑(B ⊔ C) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hx'
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  rcases quaternion_square_dichotomy B eB z zz.property.1 hz1' hz2 b hb with
    (hb1 | hbz) | hb2
  · exact Or.inr (by simpa [hb1] using hc)
  · exact Or.inr (C.mul_mem (hbz ▸ zz.property.2) hc)
  rcases quaternion_square_dichotomy C eC z zz.property.2 hz1' hz2 c hc with
    (hc1 | hcz) | hc2
  · exact Or.inl (by simpa [hc1] using hb)
  · exact Or.inl (B.mul_mem hb (hcz ▸ zz.property.1))
  have hsq : (b * c) ^ 2 = 1 := by
    rw [(show Commute b c from hcomm b hb c hc).mul_pow, hb2, hc2, ← pow_two, hz2]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [hx4] at hdvd
  norm_num at hdvd

public theorem quaternion_subgroup_eq_factor (B C D : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hD : Nonempty (D ≃* QuaternionGroup 2)) (hle : D ≤ B ⊔ C) :
    D = B ∨ D = C := by
  obtain ⟨e⟩ := hD
  let f : QuaternionGroup 2 →* G := D.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := D.subtype_injective.comp e.symm.injective
  let a := f (QuaternionGroup.a 1)
  let b := f (QuaternionGroup.xa 0)
  have haD : a ∈ D := (e.symm (QuaternionGroup.a 1)).property
  have hbD : b ∈ D := (e.symm (QuaternionGroup.xa 0)).property
  have ha4 : orderOf a = 4 := by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_a_one]
  have hb4 : orderOf b = 4 := by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_xa]
  have hnc : a * b ≠ b * a := by
    intro hh
    have heq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := hf (by simp only [map_mul]; exact hh)
    have hne : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
    exact hne heq
  have hab : (a ∈ B ∧ b ∈ B) ∨ (a ∈ C ∧ b ∈ C) := by
    rcases order_four_mem_factor B C hB hC hinter hcomm a (hle haD) ha4 with ha | ha
    · rcases order_four_mem_factor B C hB hC hinter hcomm b (hle hbD) hb4 with hb | hb
      · exact Or.inl ⟨ha, hb⟩
      · exact (hnc (hcomm a ha b hb)).elim
    · rcases order_four_mem_factor B C hB hC hinter hcomm b (hle hbD) hb4 with hb | hb
      · exact (hnc (hcomm b hb a ha).symm).elim
      · exact Or.inr ⟨ha, hb⟩
  have hgen : ∀ K : Subgroup G, a ∈ K → b ∈ K → D ≤ K := by
    intro K ha hb x hx
    let xx : D := ⟨x, hx⟩
    have hxf : f (e xx) = x := by simp [f, xx]
    rw [← hxf]
    cases e xx with
    | a i =>
      have hi : (QuaternionGroup.a i : QuaternionGroup 2) =
          QuaternionGroup.a 1 ^ i.val := by simp
      rw [hi, map_pow]
      exact K.pow_mem ha _
    | xa i =>
      have hi : (QuaternionGroup.xa i : QuaternionGroup 2) =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ i.val := by simp
      rw [hi, map_mul, map_pow]
      exact K.mul_mem hb (K.pow_mem ha _)
  have hcard : ∀ K : Subgroup G, Nonempty (K ≃* QuaternionGroup 2) →
      Nat.card K = Nat.card D := by
    intro K ⟨eK⟩
    exact (Nat.card_congr eK.toEquiv).trans (Nat.card_congr e.toEquiv).symm
  rcases hab with hab | hab
  · exact Or.inl (eq_of_le_of_card_ge (hgen B hab.1 hab.2) (hcard B hB).le)
  · exact Or.inr (eq_of_le_of_card_ge (hgen C hab.1 hab.2) (hcard C hC).le)


public theorem quaternion_factors_invariant_of_cube_eq_one (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : G ≃* G) (hjoin : (B ⊔ C).map e.toMonoidHom = B ⊔ C)
    (hcube : ∀ x : G, e (e (e x)) = x) :
    B.map e.toMonoidHom = B ∧ C.map e.toMonoidHom = C := by
  have hne : B ≠ C := by
    intro heq
    have hcard : Nat.card B = 8 := by
      obtain ⟨eB⟩ := hB
      rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← heq, inf_idem, hcard] at hinter
    omega
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hle : D ≤ B ⊔ C) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    obtain ⟨eD⟩ := hD
    apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
    · exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eD⟩
    · exact (map_mono hle).trans_eq hjoin
  have htrip (D : Subgroup G) :
      ((D.map e.toMonoidHom).map e.toMonoidHom).map e.toMonoidHom = D := by
    have hcomp : (e.toMonoidHom.comp e.toMonoidHom).comp e.toMonoidHom =
        MonoidHom.id G := by
      ext x
      exact hcube x
    rw [map_map, map_map, hcomp, map_id]
  have hleft := himage B hB le_sup_left
  have hright := himage C hC le_sup_right
  rcases hleft with hleft | hleft
  · refine ⟨hleft, ?_⟩
    rcases hright with hright | hright
    · exact (hne (map_injective e.injective (hleft.trans hright.symm))).elim
    · exact hright
  · rcases hright with hright | hright
    · have heq := htrip B
      rw [hleft, hright, hleft] at heq
      exact (hne heq.symm).elim
    · exact (hne (map_injective e.injective (hleft.trans hright.symm))).elim


public theorem quaternion_factors_invariant_of_square
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : G ≃* G) (hjoin : (B ⊔ C).map e.toMonoidHom = B ⊔ C) :
    (B.map e.toMonoidHom).map e.toMonoidHom = B ∧
      (C.map e.toMonoidHom).map e.toMonoidHom = C := by
  have hne : B ≠ C := by
    intro heq
    have hcard : Nat.card B = 8 := by
      obtain ⟨eB⟩ := hB
      rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← heq, inf_idem, hcard] at hinter
    omega
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hle : D ≤ B ⊔ C) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    obtain ⟨eD⟩ := hD
    apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
    · exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eD⟩
    · exact (map_mono hle).trans_eq hjoin
  rcases himage B hB le_sup_left with hb | hb <;>
    rcases himage C hC le_sup_right with hc | hc
  · exact (hne (map_injective e.injective (hb.trans hc.symm))).elim
  · exact ⟨by rw [hb,hb], by rw [hc,hc]⟩
  · exact ⟨by rw [hb,hc], by rw [hc,hb]⟩
  · exact (hne (map_injective e.injective (hb.trans hc.symm))).elim

end Subgroup
