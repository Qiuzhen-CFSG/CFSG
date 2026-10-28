module

public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Two-point fixers on an elementary eight-group

Two distinct nonidentity elements span a four-group. An automorphism fixing
both is determined by its value outside that four-group, giving at most four
choices. Each single-point stabilizer has index at most seven; their
intersection therefore has index at most 49 in the group of order 168.
Together these bounds force the two-point fixer to have order four.

The source consumer is the actual K-action in Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), (4.4),
pp.597–598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
/-- The pointwise stabilizer of two distinct nonidentity elements in an
 elementary group of order eight has order four. -/
theorem elementaryEight_pairFixer_card {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (z r : E) (hz : z ≠ 1) (hr : r ≠ 1) (hzr : z ≠ r) :
    Nat.card (MulAction.stabilizer (MulAut E) z ⊓
      MulAction.stabilizer (MulAut E) r : Subgroup (MulAut E)) = 4 := by
  classical
  let A := MulAction.stabilizer (MulAut E) z ⊓ MulAction.stabilizer (MulAut E) r
  let W := closure ({z,r} : Set E)
  have hp (x : E) : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) x
  let : IsKleinFour W := isKleinFour_closure_pair_of_orderOf z r
    (orderOf_eq_prime (hp z) hz) (orderOf_eq_prime (hp r) hr) hzr
    (mul_comm z r)
  have hW : Nat.card W = 4 := IsKleinFour.card_four
  have hWi : W.index = 2 := by
    have hh := W.card_mul_index
    rw [hW,hE] at hh
    omega
  have hfix (a : A) : ∀ x ∈ W, (a : MulAut E) x = x := by
    apply MonoidHom.eqOn_closure (f := a.val.toMonoidHom) (g := MonoidHom.id E)
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact a.property.1
    · have hx' : x = r := hx
      subst x
      exact a.property.2
  have hWne : W ≠ ⊤ := by intro he; rw [he,card_top,hE] at hW; omega
  obtain ⟨t,ht,htW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hWne)
  let eval : A → {x : E // x ∉ W} := fun a => ⟨a.val t,by
    intro ha
    have hh := hfix a⁻¹ _ ha
    have he : t = a.val t := by simpa only [Subgroup.coe_inv,MulAut.inv_apply_self] using hh
    exact htW (he.symm ▸ ha)⟩
  have hinj : Function.Injective eval := by
    intro a b hab
    have ht' : a.val t = b.val t := congrArg Subtype.val hab
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    by_cases hx : x ∈ W
    · exact (hfix a x hx).trans (hfix b x hx).symm
    · have htx : t⁻¹*x ∈ W := by
        rw [mul_mem_iff_of_index_two hWi]
        simp [htW,hx]
      have hh := (hfix a _ htx).trans (hfix b _ htx).symm
      simp only [map_mul,map_inv] at hh
      rw [ht'] at hh
      exact mul_left_cancel hh
  have hA : Nat.card A ≤ 4 := by
    have hc := Nat.card_le_card_of_injective eval hinj
    let : Fintype E := Fintype.ofFinite E
    have hw' : Nat.card {x : E // x ∉ W} = 4 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hE,hW]
    exact hw' ▸ hc
  have hpoint (x : E) (hx : x ≠ 1) :
      (MulAction.stabilizer (MulAut E) x).index ≤ 7 := by
    rw [MulAction.index_stabilizer]
    let f : MulAction.orbit (MulAut E) x → {y : E // y ≠ 1} := fun y => ⟨y,by
      obtain ⟨a,ha⟩ := y.property
      intro hy
      exact hx (a.injective (ha.trans hy |>.trans a.map_one.symm))⟩
    have hc := Nat.card_le_card_of_injective f
      (fun _ _ he => Subtype.ext (congrArg (fun y : {y : E // y ≠ 1} => (y : E)) he))
    let : Fintype E := Fintype.ofFinite E
    have hnon : Nat.card {y : E // y ≠ 1} = 7 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
      simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,hE]
    exact hnon ▸ hc
  have hi : A.index ≤ 49 :=
    index_inf_le.trans (Nat.mul_le_mul (hpoint z hz) (hpoint r hr))
  have hh := A.card_mul_index
  rw [card_mulAut_of_elementary_eight E hE] at hh
  change Nat.card A = 4
  nlinarith

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
