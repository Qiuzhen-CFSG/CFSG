module
public import Theory.GroupTheory.UniqueFixedCosetQuotient
public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Two selected involution classes and commuting products

Two distinct involution classes with unique fixed cosets force a subgroup to
be the whole group when the centralizers of their commuting products are
contained in it. The dihedral half-order power supplies a forbidden product
if a conjugate lies outside. Only the two selected classes are needed.

For a normal elementary binary subgroup of the stabilizer, uniqueness for
all its nonidentity elements supplies the product condition. Two different
stabilizer classes then suffice. A surjective-image version retains the
literal quotient map and lifts the fixed-coset assertions through its kernel.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 7.5, p.20, and its
application to the normal elementary quotient in 41.1, p.220.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.TwoInvolutionClassOrder
namespace UniqueFixedCoset
variable {G : Type*} [Group G]

/-- An element with a unique fixed coset has its full centralizer in the stabilizer. -/
theorem centralizer_le_of_unique {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hu : ∃! q : G ⧸ H, x • q = q) : centralizer ({x} : Set G) ≤ H := by
  intro g hg
  apply transporter_mem hx hu
  rw [mem_centralizer_singleton_iff] at hg
  rwa [hg, mul_inv_cancel_right]

/-- Unique fixed cosets give literal conjugators in the stabilizer. -/
theorem fusion_of_unique {H : Subgroup G} {a b : H}
    (hu : ∃! q : G ⧸ H, (a : G) • q = q)
    (hab : IsConj (a : G) (b : G)) : IsConj a b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact isConj_iff.mpr ⟨⟨g, transporter_mem a.property hu (hg.symm ▸ b.property)⟩,
    Subtype.ext hg⟩

/-- Source 7.5, with both selected classes and the commuting-product condition. -/
theorem eq_top_of_commuting_products [Finite G] (H : Subgroup G) (a b : H)
    (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hne : ¬ IsConj (a : G) (b : G))
    (hu : ∀ x : G, IsConj (a : G) x ∨ IsConj (b : G) x →
      ∃! q : G ⧸ H, x • q = q)
    (hprod : ∀ x y : H, IsConj (a : G) (x : G) →
      (IsConj (a : G) (y : G) ∨ IsConj (b : G) (y : G)) →
      x ≠ y → Commute x y → centralizer ({((x * y : H) : G)} : Set G) ≤ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  by_contra hg
  have haG : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha
  have hbG : orderOf (b : G) = 2 := (Subgroup.orderOf_coe b).trans hb
  let u := g * (b : G) * g⁻¹
  have hbu : IsConj (b : G) u := isConj_iff.mpr ⟨g, rfl⟩
  have huo : orderOf u = 2 := ((MulAut.conj g).orderOf_eq (b : G)).trans hbG
  have huout : u ∉ H := fun hm => hg (transporter_mem b.property
    (hu _ (Or.inr (.refl _))) hm)
  have hnu : ¬ IsConj (a : G) u := fun h => hne (h.trans hbu.symm)
  let w := halfOrder (a : G) u
  have hw := halfOrder_properties haG huo hnu (.refl _) (.refl _)
  have hcases : IsConj (a : G) ((a : G) * w) ∨ IsConj (b : G) ((a : G) * w) := by
    have he : Even (orderOf ((a : G) * u)) := by
      apply Nat.not_odd_iff_even.mp
      intro ho
      apply hnu
      exact isConj_of_involutions_odd_product _ _
        (by simpa only [haG] using pow_orderOf_eq_one (a : G))
        (by simpa only [huo] using pow_orderOf_eq_one u) ho
    have hm : orderOf ((a : G) * u) % 4 = 0 ∨ orderOf ((a : G) * u) % 4 = 2 := by
      obtain ⟨k, hk⟩ := he
      omega
    rcases hm with hm | hm
    · exact Or.inl (Theory.GroupTheory.DihedralHalfOrderClasses.preserve haG huo hm).1
    · exact Or.inr (hbu.trans
        (Theory.GroupTheory.DihedralHalfOrderClasses.exchange haG huo hm).1)
  have hwH : w ∈ H := centralizer_le_of_unique a.property
    (hu _ (Or.inl (.refl _))) (mem_centralizer_singleton_iff.mpr hw.2.1.eq)
  let v : H := a * ⟨w, hwH⟩
  have hav : a ≠ v := by
    intro he
    have he' : (1 : G) = w := mul_left_cancel
      (show (a : G) * 1 = (a : G) * w by simpa [v] using congrArg Subtype.val he)
    have hh : orderOf w = 2 := hw.1
    rw [← he', orderOf_one] at hh
    omega
  have hac : Commute a v := by
    apply (commute_iff_eq _ _).mpr
    apply Subtype.ext
    exact (Commute.refl (a : G)).mul_right hw.2.1.symm |>.eq
  have hc := hprod a v (.refl _) hcases hav hac
  have haw : ((a * v : H) : G) = w := by
    change (a : G) * ((a : G) * w) = w
    rw [← mul_assoc, show (a : G) * a = 1 by
      simpa only [haG, pow_two] using pow_orderOf_eq_one (a : G), one_mul]
  rw [haw] at hc
  exact huout (hc (mem_centralizer_singleton_iff.mpr hw.2.2.symm.eq))
end UniqueFixedCoset

namespace UniqueFixedCoset
variable {G : Type*} [Group G] [Finite G]

/-- A normal binary subgroup with two distinct stabilizer classes and unique
fixed cosets excludes a proper stabilizer. -/
theorem eq_top_of_normal_binary_subgroup (H : Subgroup G) (A : Subgroup H) [A.Normal]
    (hA : ∀ x : A, x ^ 2 = 1) (a b : A) (ha : a ≠ 1) (hb : b ≠ 1)
    (hne : ¬ IsConj (a : H) (b : H))
    (hu : ∀ x : A, x ≠ 1 → ∃! q : G ⧸ H, ((x : H) : G) • q = q) :
    H = ⊤ := by
  have ha2 : orderOf (a : H) = 2 := (Subgroup.orderOf_coe a).trans
    (orderOf_eq_prime (hA a) ha)
  have hb2 : orderOf (b : H) = 2 := (Subgroup.orderOf_coe b).trans
    (orderOf_eq_prime (hA b) hb)
  have separate : ¬ IsConj ((a : H) : G) ((b : H) : G) :=
    fun h => hne (fusion_of_unique (hu a ha) h)
  apply eq_top_of_commuting_products H a b ha2 hb2 separate
  · intro x hx
    rcases hx with hx | hx
    · exact unique_of_isConj (hu a ha) hx
    · exact unique_of_isConj (hu b hb) hx
  · intro x y hx hy hxy _
    have memA {v : A} (hv : v ≠ 1) {x : H}
        (hx : IsConj ((v : H) : G) (x : G)) : x ∈ A := by
      obtain ⟨g, hg⟩ := isConj_iff.mp (fusion_of_unique (hu v hv) hx)
      rw [← hg]
      exact Subgroup.Normal.conj_mem (inferInstance : A.Normal) _ v.property g
    have hxA := memA ha hx
    have hyA : y ∈ A := hy.elim (memA ha) (memA hb)
    have hm : x * y ∈ A := A.mul_mem hxA hyA
    have hm1 : (⟨x * y, hm⟩ : A) ≠ 1 := by
      intro he
      have hxy1 : x * y = 1 := congrArg Subtype.val he
      have hx2 : x * x = 1 := by
        have hs := congrArg A.subtype (hA ⟨x, hxA⟩)
        simpa only [map_pow, map_one, pow_two, Subgroup.subtype_apply, Subgroup.coe_mul] using hs
      exact hxy (mul_left_cancel (hx2.trans hxy1.symm))
    exact centralizer_le_of_unique (x * y).property (hu _ hm1)
end UniqueFixedCoset

namespace UniqueFixedCoset
variable {G Q : Type*} [Group G] [Group Q] [Finite Q]

/-- Apply the normal binary subgroup criterion after a literal surjection.
Each nonidentity image must have a lift with a unique fixed coset. -/
theorem eq_top_of_normal_binary_image (H : Subgroup G) (f : G →* Q)
    (hf : Function.Surjective f) (hk : f.ker ≤ H)
    (A : Subgroup (H.map f)) [A.Normal]
    (hA : ∀ x : A, x ^ 2 = 1) (a b : A) (ha : a ≠ 1) (hb : b ≠ 1)
    (hne : ¬ IsConj (a : H.map f) (b : H.map f))
    (hlift : ∀ x : A, x ≠ 1 → ∃ y : H,
      f y = ((x : H.map f) : Q) ∧ ∃! q : G ⧸ H, (y : G) • q = q) :
    H = ⊤ := by
  have he : H.map f = ⊤ := by
    apply eq_top_of_normal_binary_subgroup (H.map f) A hA a b ha hb hne
    intro x hx
    obtain ⟨y, hy, hu⟩ := hlift x hx
    rw [← hy]
    exact unique_map_of_surjective f hf hk y.property hu
  apply top_unique
  intro g _
  have hm : f g ∈ H.map f := he ▸ mem_top _
  obtain ⟨h, hh, heq⟩ := hm
  have hkg : h⁻¹ * g ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
  simpa only [mul_inv_cancel_left] using H.mul_mem hh (hk hkg)
end UniqueFixedCoset
