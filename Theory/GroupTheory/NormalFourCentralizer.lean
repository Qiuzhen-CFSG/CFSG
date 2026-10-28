module
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.IndexTwoIntersection
public import Mathlib.GroupTheory.PGroup

/-!
# The centralizer of a normal four-group

In a finite two-group a normal elementary subgroup of order four has
centralizer of index at most two. If the group contains an elementary
subgroup of order at least eight, the four-group extends to one inside
its centralizer.

Conjugation embeds the centralizer quotient in the automorphism group of
order six. For the extension, intersect a given elementary subgroup with
the centralizer and join that intersection to the four-group. If the
intersection has index two and the join does not grow, the intersection
is the four-group itself, contradicting the index-two case.

These are the rank-three consequences of GLS, volume 2, Lemma 10.20(ii),
`refs/KGroup/GLS2/ChapterC.tex`.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- A normal four-group in a finite two-group has centralizer of index one or two. -/
public theorem centralizer_index_le_two_of_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4) : (centralizer (U : Set P)).index ≤ 2 := by
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hU, IsElementaryAbelian.exponent_eq_prime⟩
  let N := normalizer (U : Set P)
  let i : P →* N :=
    { toFun g := ⟨g, by change g ∈ normalizer (U : Set P); rw [U.normalizer_eq_top]; trivial⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let f : P →* MulAut U := U.normalizerMonoidHom.comp i
  have hker : f.ker = centralizer (U : Set P) := by
    ext g
    change U.normalizerMonoidHom (i g) = 1 ↔ g ∈ centralizer (U : Set P)
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hdiv : (centralizer (U : Set P)).index ∣ 6 := by
    rw [← hker, index_ker, ← IsKleinFour.card_mulAut U]
    exact card_subgroup_dvd_card f.range
  obtain ⟨n, hn⟩ := hP.index (centralizer (U : Set P))
  have hlt : 2 ^ n < 2 ^ 3 := by
    have := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    omega
  have hnlt : n < 3 := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
  rw [hn] at hdiv ⊢
  interval_cases n <;> norm_num at *

/-- Any proper overgroup of a four-group in a finite group has order at least eight. -/
private theorem eight_le_card_of_four_lt
    {P : Type*} [Group P] [Finite P] {U V : Subgroup P}
    (hU : Nat.card U = 4) (hUV : U < V) : 8 ≤ Nat.card V := by
  have hindex : 2 ≤ U.relIndex V := by
    have hzero : U.relIndex V ≠ 0 := (U.subgroupOf V).index_ne_zero_of_finite
    have hone : U.relIndex V ≠ 1 := fun h => hUV.not_ge (relIndex_eq_one.mp h)
    omega
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup P) U V bot_le hUV.le
  simp only [relIndex_bot_left, hU] at hcard
  omega

/-- A normal four-group extends to an elementary eight in its centralizer
whenever the ambient two-group has elementary rank at least three. -/
public theorem exists_elementary_eight_above_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) :
    ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ 8 ≤ Nat.card V ∧
      U ≤ V ∧ V ≤ centralizer (U : Set P) := by
  let C := centralizer (U : Set P)
  have hUC : U ≤ C := by
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : U) (⟨u, hu⟩ : U))
  by_cases hEC : E ≤ C
  · let : IsElementaryAbelian 2 (U ⊔ E : Subgroup P) :=
      IsElementaryAbelian.sup_of_le_centralizer hEC
    exact ⟨U ⊔ E, inferInstance, hE.trans (card_le_of_le le_sup_right),
      le_sup_left, sup_le hUC hEC⟩
  have hCindex : C.index = 2 := by
    have hbound := centralizer_index_le_two_of_normal_four hP U hU
    have hzero := C.index_ne_zero_of_finite
    have hone : C.index ≠ 1 := fun h => hEC (index_eq_one.mp h ▸ le_top)
    change C.index ≤ 2 at hbound
    omega
  let B := E ⊓ C
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (congrArg (fun x : E => (x : P))
        (mul_comm (⟨a, a.property.1⟩ : E) (⟨b, b.property.1⟩ : E))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := E) a a.property.1)) }
  have hBcard : 4 ≤ Nat.card B := by
    have hindex := C.subgroupOf_index_eq_two E hCindex hEC
    have hcard := relIndex_mul_relIndex (⊥ : Subgroup P) B E bot_le inf_le_left
    have hrel : B.relIndex E = 2 := by
      rw [show B = E ⊓ C from rfl, inf_relIndex_left]
      exact hindex
    simp only [relIndex_bot_left, hrel] at hcard
    omega
  have hBU : ¬ B ≤ U := by
    intro hle
    have heq : B = U := eq_of_le_of_card_ge hle (by omega)
    have hUE : U ≤ E := heq ▸ (inf_le_left : B ≤ E)
    apply hEC
    intro e he u hu
    exact congrArg Subtype.val (mul_comm (⟨u, hUE hu⟩ : E) (⟨e, he⟩ : E))
  have hcomm : B ≤ centralizer (U : Set P) := inf_le_right
  let : IsElementaryAbelian 2 (U ⊔ B : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  refine ⟨U ⊔ B, inferInstance, ?_, le_sup_left, sup_le hUC inf_le_right⟩
  exact eight_le_card_of_four_lt hU (lt_of_le_of_ne le_sup_left (by
    intro heq
    exact hBU (heq ▸ le_sup_right)))

/-- Every involution in the centralizer of a normal four-group lies in an
elementary eight, provided the ambient two-group has elementary rank at least three. -/
public theorem exists_elementary_eight_of_mem_centralizer_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (t : P) (ht : t ^ 2 = 1) (htC : t ∈ centralizer (U : Set P)) :
    ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ 8 ≤ Nat.card V ∧ t ∈ V := by
  by_cases htU : t ∈ U
  · obtain ⟨V, hV, hcard, hUV, _⟩ := exists_elementary_eight_above_normal_four hP U hU E hE
    exact ⟨V, hV, hcard, hUV htU⟩
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht
  let : IsElementaryAbelian 2 (U ⊔ zpowers t : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htC)
  refine ⟨U ⊔ zpowers t, inferInstance, ?_, (le_sup_right : zpowers t ≤ U ⊔ zpowers t) (mem_zpowers t)⟩
  exact eight_le_card_of_four_lt hU (lt_of_le_of_ne le_sup_left (by
    intro heq
    exact htU (heq ▸ (le_sup_right : zpowers t ≤ U ⊔ zpowers t) (mem_zpowers t))))

end Subgroup
