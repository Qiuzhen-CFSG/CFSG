module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwoBasic
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.NoOrder15
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Order obstructions to a local A₈ section in sporadic models

An A₈ section forces 20160 to divide the ambient order, excluding M₁₁,
M₁₂ and J₁. It also forces an element of order fifteen: lift the disjoint
three-cycle and five-cycle and take a power of its preimage. The proved
M₂₂ spectrum excludes that row without assumptions on the section kernel.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, as used in 15.3.32(3),
printed p.1133. The carriers and the M₂₂ spectrum are the literal models
in the source catalogue.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

private def fifteen : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 4 5 *
      Equiv.swap 5 6 * Equiv.swap 6 7,
   by simp [Equiv.Perm.mem_alternatingGroup, map_mul]⟩

private theorem fifteen_order : orderOf fifteen = 15 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · apply Subtype.ext
    decide +kernel
  · intro p hp hd
    have hcases : p = 3 ∨ p = 5 := by
      have h : p ∣ 3 * 5 := hd
      rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    rcases hcases with rfl | rfl <;> decide +kernel

/-- The literal A₈ quotient forces an element of order fifteen in the ambient group. -/
theorem exists_order_fifteen {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    ∃ x : G, orderOf x = 15 := by
  obtain ⟨e⟩ := quotient_equiv h
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  obtain ⟨b, hb⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 B)) fifteen
  have hd : 15 ∣ orderOf b := by
    have hh := orderOf_map_dvd f b
    rw [show f b = fifteen from hb, fifteen_order] at hh
    exact hh
  refine ⟨(b ^ (orderOf b / 15) : B), ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (isOfFinOrder_of_finite b).orderOf_pos.ne' hd

omit [Finite G] in
/-- M₁₁ cannot contain the supplied A₈ section. -/
theorem not_mathieu_eleven {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M11) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m11_order] at hd
  norm_num at hd

omit [Finite G] in
/-- M₁₂ cannot contain the supplied A₈ section. -/
theorem not_mathieu_twelve {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M12) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order] at hd
  norm_num at hd

omit [Finite G] in
/-- The additional J₁ model cannot contain the supplied A₈ section. -/
theorem not_janko_one {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Janko1.Model) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hd
  norm_num at hd

/-- M₂₂ has no A₈ section, since it has no element of order fifteen. -/
theorem not_mathieu_twentyTwo {B : Subgroup G}
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.Mathieu.M22) : False := by
  obtain ⟨x, hx⟩ := exists_order_fifteen h
  exact Sporadic.Mathieu.m22_orderOf_ne_fifteen (e x) ((e.orderOf_eq x).trans hx)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
