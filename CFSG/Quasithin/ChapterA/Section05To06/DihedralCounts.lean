module

public import CFSG.Quasithin.ChapterA.Section05To06.Counting
public import Theory.GroupTheory.DihedralHalfOrderClasses

/-!
# The dihedral pair-count bounds of A.6.2

For a mixed pair `(u,v)` whose cyclic product subgroup contains the involution
`x`, cyclic uniqueness identifies `x` with the half-order power. This element
centralizes both factors. The explicit dihedral conjugation calculations
preserve the reflection classes when the product order is zero modulo four
and exchange them when it is two modulo four. Ambient nonconjugacy then
supplies the exclusions in `B2` and `C2`.

Each bound comes from an injection of the literal `A1` or `A2` into the
corresponding product of sets. Depending on the class of `x`, the injection
keeps or swaps the two coordinates. Thus the result holds for every involution
`x` and every representative `y` of the other class.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.6.2,
printed p. 64 (PDF p. 75).
-/

public section

namespace CFSG.Quasithin.ChapterA.Section05To06
open Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G]

private theorem conj_order {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

private theorem class_alignment {z t x y : G} (h : TwoInvolutionClasses z t)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : ¬ IsConj x y) :
    (IsConj x z ∧ IsConj y t) ∨ (IsConj x t ∧ IsConj y z) := by
  rcases h.exhaustive x hx with hz | ht
  · rcases h.exhaustive y hy with hz' | ht'
    · exact False.elim (hxy (hz.symm.trans hz'))
    · exact Or.inl ⟨hz.symm, ht'.symm⟩
  · rcases h.exhaustive y hy with hz' | ht'
    · exact Or.inr ⟨ht.symm, hz'.symm⟩
    · exact False.elim (hxy (ht.symm.trans ht'))

/-- The injection is the pair itself or its coordinate swap, according to
which of the two fixed classes contains `x`. -/
private theorem pair_card_bound [Finite G] {z t x y : G}
    (h : TwoInvolutionClasses z t) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : ¬ IsConj x y) (S : Set (G × G)) (P : G → Prop)
    (hS : ∀ p ∈ S, IsConj z p.1 ∧ IsConj t p.2 ∧ P p.1 ∧ P p.2) :
    Nat.card S ≤ Nat.card {u : G // IsConj x u ∧ P u} *
      Nat.card {u : G // IsConj y u ∧ P u} := by
  rw [← Nat.card_prod]
  rcases class_alignment h hx hy hxy with ⟨hxz, hyt⟩ | ⟨hxt, hyz⟩
  · let f : S → {u : G // IsConj x u ∧ P u} × {u : G // IsConj y u ∧ P u} :=
      fun p => (⟨p.val.1, hxz.trans (hS p.val p.property).1,
        (hS p.val p.property).2.2.1⟩,
        ⟨p.val.2, hyt.trans (hS p.val p.property).2.1, (hS p.val p.property).2.2.2⟩)
    apply Nat.card_le_card_of_injective f
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext (congrArg (fun v => v.1.val) hpq) (congrArg (fun v => v.2.val) hpq)
  · let f : S → {u : G // IsConj x u ∧ P u} × {u : G // IsConj y u ∧ P u} :=
      fun p => (⟨p.val.2, hxt.trans (hS p.val p.property).2.1,
        (hS p.val p.property).2.2.2⟩,
        ⟨p.val.1, hyz.trans (hS p.val p.property).1, (hS p.val p.property).2.2.1⟩)
    apply Nat.card_le_card_of_injective f
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext (congrArg (fun v => v.2.val) hpq) (congrArg (fun v => v.1.val) hpq)

/-- A.6.2 for the pairs whose product order is divisible by four. -/
theorem a1_le_b1_mul_c1 [Finite G] {z t x y : G}
    (h : TwoInvolutionClasses z t) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : ¬ IsConj x y) : a1 z t x ≤ b1 x * c1 x y := by
  apply pair_card_bound h hx hy hxy (A1 z t x)
    (fun u => Commute u x ∧ IsConj u (u * x))
  intro p hp
  obtain ⟨⟨hu, hv, hm⟩, hn⟩ := hp
  have he := (mem_zpowers_iff_halfOrder h hx hu hv).mp hm
  have hc := halfOrder_properties h.order_z h.order_t h.distinct hu hv
  have hr := Theory.GroupTheory.DihedralHalfOrderClasses.preserve
    ((conj_order hu).symm.trans h.order_z) ((conj_order hv).symm.trans h.order_t) hn
  rw [he] at hc hr
  exact ⟨hu, hv, ⟨hc.2.1.symm, hr.1⟩, ⟨hc.2.2.symm, hr.2⟩⟩

/-- A.6.2 for the pairs whose product order is two modulo four. Ambient
nonconjugacy excludes fusion of a reflection with its half-order translate. -/
theorem a2_le_b2_mul_c2 [Finite G] {z t x y : G}
    (h : TwoInvolutionClasses z t) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : ¬ IsConj x y) : a2 z t x ≤ b2 x * c2 x y := by
  apply pair_card_bound h hx hy hxy (A2 z t x)
    (fun u => Commute u x ∧ ¬ IsConj u (u * x))
  intro p hp
  obtain ⟨⟨hu, hv, hm⟩, hn⟩ := hp
  have he := (mem_zpowers_iff_halfOrder h hx hu hv).mp hm
  have hc := halfOrder_properties h.order_z h.order_t h.distinct hu hv
  have hr := Theory.GroupTheory.DihedralHalfOrderClasses.exchange
    ((conj_order hu).symm.trans h.order_z) ((conj_order hv).symm.trans h.order_t) hn
  rw [he] at hc hr
  have hne : ¬ IsConj p.1 p.2 := fun hh => h.distinct (hu.trans (hh.trans hv.symm))
  exact ⟨hu, hv, ⟨hc.2.1.symm, fun hh => hne (hh.trans hr.1.symm)⟩,
    ⟨hc.2.2.symm, fun hh => hne (hr.2.trans hh.symm)⟩⟩

/-- A.6.2, both inequalities for arbitrary opposite-class involutions. -/
theorem lemma_A_6_2 [Finite G] {z t x y : G}
    (h : TwoInvolutionClasses z t) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : ¬ IsConj x y) :
    a1 z t x ≤ b1 x * c1 x y ∧ a2 z t x ≤ b2 x * c2 x y :=
  ⟨a1_le_b1_mul_c1 h hx hy hxy, a2_le_b2_mul_c2 h hx hy hxy⟩

/-- The first inequality at the representative `z`, used in A.6.4. -/
theorem a1_z_le [Finite G] {z t : G} (h : TwoInvolutionClasses z t) :
    a1 z t z ≤ b1 z * c1 z t :=
  a1_le_b1_mul_c1 h h.order_z h.order_t h.distinct

/-- The second inequality at the representative `z`, used in A.6.4. -/
theorem a2_z_le [Finite G] {z t : G} (h : TwoInvolutionClasses z t) :
    a2 z t z ≤ b2 z * c2 z t :=
  a2_le_b2_mul_c2 h h.order_z h.order_t h.distinct

/-- The first inequality at the representative `t`, used in A.6.4. -/
theorem a1_t_le [Finite G] {z t : G} (h : TwoInvolutionClasses z t) :
    a1 z t t ≤ b1 t * c1 t z :=
  a1_le_b1_mul_c1 h h.order_t h.order_z (fun hh => h.distinct hh.symm)

/-- The second inequality at the representative `t`, used in A.6.4. -/
theorem a2_t_le [Finite G] {z t : G} (h : TwoInvolutionClasses z t) :
    a2 z t t ≤ b2 t * c2 t z :=
  a2_le_b2_mul_c2 h h.order_t h.order_z (fun hh => h.distinct hh.symm)

end CFSG.Quasithin.ChapterA.Section05To06

end
