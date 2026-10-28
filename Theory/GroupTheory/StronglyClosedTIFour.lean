module

public import Theory.GroupTheory.SetStrongClosure
public import Theory.GroupTheory.ZStar.OddProductConjugator
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic.Group

/-!
# Strongly closed elementary TI subgroups

An elementary abelian two-subgroup which is TI and strongly closed in its
normalizer has a transitive normalizer on its nonidentity elements whenever
that normalizer is proper. An even-order product of involutions would supply
a central involution; strong closure and TI then contradict the choice of an
escaping conjugate. Odd-order products supply the required conjugators.

For a four-group, a two-group normalizer is therefore the whole ambient group:
a nontrivial central element in the normal four-subgroup is fixed by the
normalizer, which rules out transitivity on its three nonidentity elements.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemma 1.1, printed p.32, and its application in Lemma 2.8(1), p.36.
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf
-/

open Subgroup BenderSuzuki.PFAppendixIII
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem closed_of_conj (U : Subgroup G)
    (hs : IsStronglyClosedSet (U : Set G) (normalizer (U : Set G)) ⊤)
    {x y : G} (hx : x ∈ U) (hc : IsConj x y)
    (hy : y ∈ normalizer (U : Set G)) : y ∈ U := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hc
  change a * x * a⁻¹ ∈ (U : Set G)
  simpa only [inv_inv] using hs.2 x hx a⁻¹ (mem_top _) (by simpa using hy)

omit [Finite G] in
private theorem ti_commuting_mem (U : Subgroup G)
    (hti : ∀ a x : G, x ∈ U → x ≠ 1 → a * x * a⁻¹ ∈ U →
      a ∈ normalizer (U : Set G))
    {x a : G} (hx : x ∈ U) (hx1 : x ≠ 1) (ha : Commute a x) :
    a ∈ normalizer (U : Set G) := by
  apply hti a x hx hx1
  simpa only [ha.eq, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- Aschbacher's elementary TI transitivity lemma, with the transporter and
strong-closure conventions made explicit. -/
public theorem ti_stronglyClosed_normalizer_transitive (U : Subgroup G)
    (hel : IsElementaryAbelian 2 U)
    (hti : ∀ a x : G, x ∈ U → x ≠ 1 → a * x * a⁻¹ ∈ U →
      a ∈ normalizer (U : Set G))
    (hs : IsStronglyClosedSet (U : Set G) (normalizer (U : Set G)) ⊤)
    (hproper : normalizer (U : Set G) ≠ ⊤)
    {e f : G} (he : e ∈ U) (he1 : e ≠ 1) (hf : f ∈ U) (hf1 : f ≠ 1) :
    ∃ a ∈ normalizer (U : Set G), a * e * a⁻¹ = f := by
  classical
  let _ := hel
  obtain ⟨g, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hgN : g ∉ normalizer (U : Set G) := hg.2
  let a := g * e * g⁻¹
  have hea : IsConj e a := isConj_iff.mpr ⟨g, rfl⟩
  have haU : a ∉ U := fun ha => hgN (hti g e he he1 ha)
  have haN : a ∉ normalizer (U : Set G) := fun ha =>
    haU (closed_of_conj U hs he hea ha)
  have heI : IsInvolution e := ⟨he1, elemPow_eq_one_of_isElementaryAbelian e he⟩
  have hfI : IsInvolution f := ⟨hf1, elemPow_eq_one_of_isElementaryAbelian f hf⟩
  have haI : IsInvolution a := by
    simpa [a, rightConjugateElem] using isInvolution_rightConjugateElem (g := g⁻¹) heI
  have haf : a ≠ f := fun hh => haU (hh ▸ hf)
  have hodd : Odd (orderOf (a * f)) := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨m, hm⟩
    have hm' : orderOf (a * f) = 2 * m := by omega
    obtain ⟨hzI, hza, hzf⟩ :=
      BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii haI hfI haf hm'
    let z := (a * f) ^ m
    have hzI' : IsInvolution z := hzI
    have hrN : z * f ∈ normalizer (U : Set G) :=
      ti_commuting_mem U hti hf hf1 (hzf.mul_left (Commute.refl f))
    have hrU : z * f ∈ U := by
      obtain ⟨k, hk | hk⟩ := m.even_or_odd'
      · have hc : IsConj f (z * f) := by
          apply isConj_iff.mpr
          refine ⟨(a * f) ^ k, ?_⟩
          simpa only [z, hk] using
            Glauberman.ZStar.conjugate_second_by_product_pow haI hfI k
        exact closed_of_conj U hs hf hc hrN
      · have hc : IsConj a (z * f) := by
          apply isConj_iff.mpr
          refine ⟨(a * f) ^ k, ?_⟩
          simpa only [z, hk] using
            Glauberman.ZStar.conjugate_first_by_product_pow haI hfI k
        exact closed_of_conj U hs he (hea.trans hc) hrN
    have hzU : z ∈ U := by
      simpa only [mul_inv_cancel_right] using U.mul_mem hrU (U.inv_mem hf)
    exact haN (ti_commuting_mem U hti hzU hzI'.ne_one hza.symm)
  obtain ⟨y, hy, -⟩ :=
    Glauberman.ZStar.exists_conjugator_of_involutions_mul_odd haI hfI hodd
  have hef : IsConj e f := hea.trans (isConj_iff.mpr ⟨y, hy⟩).symm
  obtain ⟨b, hb⟩ := isConj_iff.mp hef
  exact ⟨b, hti b e he he1 (hb.symm ▸ hf), hb⟩

/-- A strongly closed elementary TI four-group with a two-group normalizer
is normal in the ambient finite group. -/
public theorem normalizer_eq_top_of_stronglyClosed_ti_four (U : Subgroup G)
    (hel : IsElementaryAbelian 2 U) (hcard : Nat.card U = 4)
    (hti : ∀ a x : G, x ∈ U → x ≠ 1 → a * x * a⁻¹ ∈ U →
      a ∈ normalizer (U : Set G))
    (hs : IsStronglyClosedSet (U : Set G) (normalizer (U : Set G)) ⊤)
    (hN : IsPGroup 2 (normalizer (U : Set G))) :
    normalizer (U : Set G) = ⊤ := by
  classical
  by_contra hproper
  let N := normalizer (U : Set G)
  let V := U.subgroupOf N
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 N) := ⟨hN⟩
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial V := (subgroupOfEquivOfLe U.le_normalizer).toEquiv.nontrivial
  obtain ⟨e, he1, heZ⟩ := exists_nontrivial_center_mem_normal V (p := 2)
  have he1' : ((e : N) : G) ≠ 1 := fun hh => he1 (Subtype.ext (Subtype.ext hh))
  have hall (f : U) (hf : f ≠ 1) : (f : G) = ((e : N) : G) := by
    obtain ⟨b, hb, hbf⟩ := ti_stronglyClosed_normalizer_transitive U hel hti hs hproper
      e.property he1' f.property (fun hh => hf (Subtype.ext hh))
    have hcomm := congrArg Subtype.val ((mem_center_iff.mp heZ) ⟨b, hb⟩)
    change b * ((e : N) : G) = ((e : N) : G) * b at hcomm
    change b * ((e : N) : G) * b⁻¹ = (f : G) at hbf
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at hbf
    exact hbf.symm
  have hinj : Function.Injective (fun f : U => decide (f = 1)) := by
    intro x y hxy
    by_cases hx : x = 1
    · have hy : y = 1 := by simpa [hx] using hxy.symm
      exact hx.trans hy.symm
    · have hy : y ≠ 1 := by simpa [hx] using hxy.symm
      exact Subtype.ext ((hall x hx).trans (hall y hy).symm)
  have hb := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at hb
  omega

end Theory.GroupTheory
