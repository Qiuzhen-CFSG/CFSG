module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Fusion from four-group cross actions

Suppose four elementary abelian subgroups `V`, `V₁`, `W`, `W₁` have order
four, the first two normalize `W ⊔ W₁`, and the pairs `(V,W)`, `(V₁,W₁)`,
`(W,W₁)` centralize one another. If every nonidentity actor fails to commute
with every nonidentity element of the opposite factor, all nonidentity
elements of `W` are conjugate in the ambient group.

An involution `a` centralizing `W` must act trivially modulo `W`: writing
`b^a = w*c` with `b,c ∈ W₁`, its square relation implies that `bc` is fixed,
so the cross-action hypothesis forces `c = b`. For fixed nonidentity `b`,
the displacement map from `V` to `W` is injective and hence surjective.
The symmetric statement for `V₁` gives a conjugacy chain
`x ~ x*t ~ y*t ~ y`, for any nonidentity `x,y ∈ W` and `t ∈ W₁`.

This is Janko–Thompson, *On Finite Simple Groups whose Sylow 2-Subgroups
have no Normal Elementary Subgroups of Order 8*, Math. Z. 113 (1970),
Lemma 2.1, pp.386–387.
The orbit argument replaces the source's final generator calculation.
Source: `refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup
open scoped IsMulCommutative

private theorem shear_displacement_mem
    {G : Type*} [Group G] (W U : Subgroup G)
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 U]
    (hWU : W ≤ centralizer (U : Set G))
    (a : G) (ha : a * a = 1)
    (han : a ∈ normalizer ((W ⊔ U : Subgroup G) : Set G))
    (hac : a ∈ centralizer (W : Set G))
    (hfree : ∀ u ∈ U, u ≠ 1 → ¬ Commute a u)
    (b : G) (hb : b ∈ U) :
    a * b * a⁻¹ * b⁻¹ ∈ W := by
  let f := MulAut.conj a
  have hf2 (x : G) : f (f x) = x := by
    change a * (a * x * a⁻¹) * a⁻¹ = x
    calc
      _ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [ha]; simp
  have hfix (w : G) (hw : w ∈ W) : f w = w := by
    change a * w * a⁻¹ = w
    rw [← hac w hw, mul_inv_cancel_right]
  have hmem : f b ∈ W ⊔ U :=
    (mem_normalizer_iff.mp han b).mp ((show U ≤ W ⊔ U from le_sup_right) hb)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right W U
    (hWU.trans (centralizer_le_normalizer _))] at hmem
  obtain ⟨w, hw, c, hc, hbc⟩ := hmem
  have hw2 : w * w = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
  have hcimage : f c = w * b := by
    have hh : b = w * f c := by
      calc
        b = f (f b) := (hf2 b).symm
        _ = w * f c := by rw [← hbc, map_mul, hfix w hw]
    rw [hh, ← mul_assoc, hw2, one_mul]
  have hbcfix : f (b * c) = b * c := by
    rw [map_mul, ← hbc, hcimage]
    calc
      (w * c) * (w * b) = w * (c * w) * b := by group
      _ = w * (w * c) * b := by rw [hWU hw c hc]
      _ = c * b := by rw [← mul_assoc w w c, hw2, one_mul]
      _ = b * c := congrArg Subtype.val (mul_comm (⟨c, hc⟩ : U) ⟨b, hb⟩)
  have hbc1 : b * c = 1 := by
    by_contra hne
    exact hfree (b * c) (U.mul_mem hb hc) hne
      (mul_inv_eq_iff_eq_mul.mp hbcfix)
  have hcb : c = b := by
    have hb2 : b * b = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
    exact mul_left_cancel (hbc1.trans hb2.symm)
  change f b * b⁻¹ ∈ W
  rw [← hbc, hcb, mul_inv_cancel_right]
  exact hw

private theorem cross_coset_conjugate
    {G : Type*} [Group G] [Finite G] (V W U : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 U]
    (hcard : Nat.card V = Nat.card W)
    (hWU : W ≤ centralizer (U : Set G))
    (hn : V ≤ normalizer ((W ⊔ U : Subgroup G) : Set G))
    (hc : V ≤ centralizer (W : Set G))
    (hfree : ∀ a ∈ V, a ≠ 1 → ∀ u ∈ U, u ≠ 1 → ¬ Commute a u)
    (b : G) (hb : b ∈ U) (hb1 : b ≠ 1)
    (d : G) (hd : d ∈ W) :
    ∃ a ∈ V, a * b * a⁻¹ = d * b := by
  have hmem (a : V) : (a : G) * b * (a : G)⁻¹ * b⁻¹ ∈ W := by
    by_cases ha1 : (a : G) = 1
    · simp [ha1]
    · exact shear_displacement_mem W U hWU a
        (by simpa only [pow_two] using
          elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property)
        (hn a.property) (hc a.property) (hfree a a.property ha1) b hb
  let δ : V → W := fun a => ⟨(a : G) * b * (a : G)⁻¹ * b⁻¹, hmem a⟩
  have hinj : Function.Injective δ := by
    intro a₁ a₂ heq
    have heq' : (a₁ : G) * b * (a₁ : G)⁻¹ =
        (a₂ : G) * b * (a₂ : G)⁻¹ :=
      mul_right_cancel (congrArg Subtype.val heq)
    have hcomm : Commute ((a₂ : G)⁻¹ * a₁) b := by
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        ((a₂ : G)⁻¹ * a₁) * b * ((a₂ : G)⁻¹ * a₁)⁻¹ =
            (a₂ : G)⁻¹ * ((a₁ : G) * b * (a₁ : G)⁻¹) * a₂ := by group
        _ = (a₂ : G)⁻¹ * ((a₂ : G) * b * (a₂ : G)⁻¹) * a₂ := by rw [heq']
        _ = b := by group
    have hquot : (a₂ : G)⁻¹ * a₁ = 1 := by
      by_contra hne
      exact hfree _ (V.mul_mem (V.inv_mem a₂.property) a₁.property) hne b hb hb1 hcomm
    exact Subtype.ext (inv_mul_eq_one.mp hquot).symm
  obtain ⟨a, ha⟩ := ((Nat.bijective_iff_injective_and_card δ).mpr ⟨hinj, hcard⟩).2
    (⟨d, hd⟩ : W)
  refine ⟨a, a.property, ?_⟩
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val ha)

/-- The three nonidentity elements of `W` fuse in the four-group cross-action configuration. -/
public theorem isConj_of_four_group_cross_action
    {G : Type*} [Group G] [Finite G]
    (V V₁ W W₁ : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 V₁]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 W₁]
    (hV : Nat.card V = 4) (hV₁ : Nat.card V₁ = 4)
    (hW : Nat.card W = 4) (hW₁ : Nat.card W₁ = 4)
    (hn : V ⊔ V₁ ≤ normalizer ((W ⊔ W₁ : Subgroup G) : Set G))
    (hVW : V ≤ centralizer (W : Set G))
    (hV₁W₁ : V₁ ≤ centralizer (W₁ : Set G))
    (hWW₁ : W ≤ centralizer (W₁ : Set G))
    (_hdisjoint : W ⊓ W₁ = ⊥)
    (hcross : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ W₁, w ≠ 1 → ¬ Commute v w)
    (hcross₁ : ∀ v ∈ V₁, v ≠ 1 → ∀ w ∈ W, w ≠ 1 → ¬ Commute v w)
    (x y : G) (hx : x ∈ W) (hy : y ∈ W) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    IsConj x y := by
  have hnV : V ≤ normalizer ((W ⊔ W₁ : Subgroup G) : Set G) :=
    le_sup_left.trans hn
  have hnV₁ : V₁ ≤ normalizer ((W₁ ⊔ W : Subgroup G) : Set G) := by
    simpa only [sup_comm W W₁] using (le_sup_right.trans hn :
      V₁ ≤ normalizer ((W ⊔ W₁ : Subgroup G) : Set G))
  have hW₁W : W₁ ≤ centralizer (W : Set G) := le_centralizer_iff.mp hWW₁
  let : Nontrivial W₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW₁]; decide)
  obtain ⟨t, ht⟩ := exists_ne (1 : W₁)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  have hcoset (z : G) (hz : z ∈ W) (hz1 : z ≠ 1) : IsConj z (z * t) := by
    obtain ⟨a, _, ha⟩ := cross_coset_conjugate V₁ W₁ W (hV₁.trans hW₁.symm)
      hW₁W hnV₁ hV₁W₁ hcross₁ z hz hz1 t t.property
    exact isConj_iff.mpr ⟨a, ha.trans (hWW₁ hz t t.property)⟩
  obtain ⟨a, haV, ha⟩ := cross_coset_conjugate V W W₁ (hV.trans hW.symm)
    hWW₁ hnV hVW hcross t t.property ht1 (x⁻¹ * y) (W.mul_mem (W.inv_mem hx) hy)
  have hfix : a * x * a⁻¹ = x := by
    rw [← hVW haV x hx, mul_inv_cancel_right]
  have hmiddle : IsConj (x * t) (y * t) := by
    apply isConj_iff.mpr
    refine ⟨a, ?_⟩
    calc
      a * (x * t) * a⁻¹ = (a * x * a⁻¹) * (a * t * a⁻¹) := by group
      _ = x * ((x⁻¹ * y) * t) := by rw [hfix, ha]
      _ = y * t := by group
  exact (hcoset x hx hx1).trans (hmiddle.trans (hcoset y hy hy1).symm)

end Subgroup
