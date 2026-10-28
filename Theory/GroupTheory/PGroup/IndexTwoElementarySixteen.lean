module

public import Theory.GroupTheory.PGroup.MaximalElementaryCentralizer
public import Mathlib.GroupTheory.IndexNormal

/-!
# A normal elementary eight from an index-two elementary sixteen

Let an elementary subgroup E of order sixteen be normalized by an index-two
subgroup T. If E is of largest elementary order and its centralizer in T has
index at most two, then the normal core of E has order at least eight.

Choose a representative a for the other coset of T. The intersection of E
with the a-conjugate of C_T(E) has index at most two in E. Its elements have
square one and centralize the a-conjugate of E, so maximality puts them in
that conjugate. The two cosets of T then put the intersection in the normal
core of E. This gives the contradiction to absence of normal elementary
eights without requiring an exact intersection order or center calculation.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, p.388,
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- An elementary sixteen with small centralizer index in an index-two
normalizing overgroup contains an ambient normal elementary eight or larger. -/
public theorem exists_normal_elementary_eight_of_sixteen_of_centralizer_index_le_two
    {P : Type*} [Group P] [Finite P]
    (T E : Subgroup P) (hT : T.index = 2)
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set P))
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 16)
    (hbound : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A ≤ 16)
    (hindex : (centralizer (E : Set P)).relIndex T ≤ 2) :
    ∃ R : Subgroup P, R.Normal ∧ IsElementaryAbelian 2 R ∧ 8 ≤ Nat.card R := by
  classical
  let : T.Normal := T.normal_of_index_eq_two hT
  obtain ⟨a, ha⟩ := T.index_dvd_two_iff.mp (hT ▸ dvd_rfl)
  let f := (MulAut.conj a).toMonoidHom
  let F := E.map f
  let C := (T ⊓ centralizer (E : Set P)).map f
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map f
  have hF : Nat.card F = 16 := (card_map_of_injective (MulAut.conj a).injective).trans hE
  have hTmap : T.map f = T := mem_normalizer_iff_map_conj_eq.mp
    (T.normalizer_eq_top ▸ mem_top a)
  have hCindex : C.relIndex T ≤ 2 := by
    rw [← hTmap, relIndex_map_map_of_injective _ _ (MulAut.conj a).injective]
    simpa only [inf_relIndex_left] using hindex
  have hCF : C ≤ centralizer (F : Set P) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨e, he, rfl⟩
    simpa only [map_mul] using congrArg f (hc.2 e he)
  have hRC : E ⊓ C ≤ E.normalCore := by
    intro x hx g
    have hxF : x ∈ F := mem_of_pow_eq_one_of_elementary_card_le F
      (by simpa only [hF] using hbound)
      (elemPow_eq_one_of_isElementaryAbelian x hx.1) (hCF hx.2)
    have hxconj : a⁻¹ * x * a ∈ E := mem_map_equiv.mp hxF
    rcases ha g with hg | hg
    · have hm := (mem_normalizer_iff.mp (hTE hg) (a⁻¹ * x * a)).mp hxconj
      convert hm using 1
      group
    · exact (mem_normalizer_iff.mp (hTE hg) x).mp hx.1
  have hCE : C.relIndex E ≤ 2 :=
    (relIndex_le_of_le_right hET index_ne_zero_of_finite).trans hCindex
  have hcard : Nat.card (E ⊓ C : Subgroup P) * C.relIndex E = 16 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup P) (E ⊓ C) E bot_le inf_le_left
    simpa only [relIndex_bot_left, inf_relIndex_left, hE] using hh
  have hlarge : 8 ≤ Nat.card E.normalCore := by
    have hlower : 8 ≤ Nat.card (E ⊓ C : Subgroup P) := by nlinarith
    exact hlower.trans (card_le_of_le hRC)
  have hsquare (x : E.normalCore) : x ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : P) (E.normalCore_le x.property))
  have he : IsElementaryAbelian 2 E.normalCore :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun e : E => (e : P))
        (mul_comm (⟨x, E.normalCore_le x.property⟩ : E)
          (⟨y, E.normalCore_le y.property⟩ : E)))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsquare }
  exact ⟨E.normalCore, inferInstance, he, hlarge⟩

end Subgroup
