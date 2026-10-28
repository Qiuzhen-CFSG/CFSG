module
public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Restriction groups and removal of an overlap twist

The automorphisms extending along a fixed endpoint map form a subgroup of
all overlap automorphisms. A twist is removable exactly when it belongs to
the product of the two restriction groups, with the order and inverse in
`FactorsThrough`; this is equivalent to an isomorphism of the twisted and
original amalgams, retaining both commuting squares.

For a finite overlap, suppose its automorphism group has order at most `4*n`,
each endpoint restriction group has order at least `2*n`, and their
intersection has order at most `n`, where `n > 0`. The restriction groups
have index at most two and hence are normal. The subgroup product formula
then forces their product to be the whole automorphism group. This yields
rigidity of every parabolically equivalent Sylow amalgam.

These are elementary group-theoretic reductions for the finite calculations
underlying Aschbacher--Smith F.1.11--12, printed pp.262--264. The numerical
premises are not asserted for any particular model in this module.
-/

@[expose] public section
open scoped Pointwise

namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

/-- The actual image of endpoint restriction, specified by compatible extensions. -/
def extensionSubgroup (i : B →* L) : Subgroup (MulAut B) where
  carrier := ExtendsAcross i
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, fun x => by simp only [MulAut.mul_apply, hb, ha]⟩
  inv_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a.symm, fun x => ?_⟩
    apply a.injective
    simpa using (ha (f.symm x)).symm

private theorem large_subgroup_product {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (n : ℕ) (hn : 0 < n) (hg : Nat.card G ≤ 4 * n)
    (hh : 2 * n ≤ Nat.card H) (hk : 2 * n ≤ Nat.card K)
    (hi : Nat.card (H ⊓ K : Subgroup G) ≤ n) :
    ∀ x : G, ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hidx : H.index ≤ 2 := by
    have hc := H.card_mul_index
    have hm := Nat.mul_le_mul_right H.index hh
    nlinarith
  have hnH : H.Normal := by
    have hp := H.index_ne_zero_of_finite
    have hc : H.index = 1 ∨ H.index = 2 := by omega
    rcases hc with hc | hc
    · rw [H.index_eq_one.mp hc]
      infer_instance
    · exact H.normal_of_index_eq_two hc
  let : H.Normal := hnH
  have hnorm : K ≤ Subgroup.normalizer (H : Set G) := by
    rw [H.normalizer_eq_top]
    exact le_top
  have hcount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes H K hnorm
  have hsup : H ⊔ K = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hs := Subgroup.card_le_card_group (H ⊔ K)
    have hm := Nat.mul_le_mul hh hk
    have hi' := Nat.mul_le_mul_right (Nat.card (H ⊔ K : Subgroup G)) hi
    nlinarith
  intro x
  have hx : x ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H K hnorm, hsup]
    trivial
  obtain ⟨h, hh, k, hk, hx⟩ := hx
  exact ⟨h, hh, k, hk, hx.symm⟩

/-- Bounds on the two restriction groups and their intersection remove every twist. -/
theorem factorsThrough_of_counts [Finite B] (β : RankTwoAmalgam L B R)
    (n : ℕ) (hn : 0 < n) (hg : Nat.card (MulAut B) ≤ 4 * n)
    (hleft : 2 * n ≤ Nat.card (extensionSubgroup β.left))
    (hright : 2 * n ≤ Nat.card (extensionSubgroup β.right))
    (hinter : Nat.card (extensionSubgroup β.left ⊓ extensionSubgroup β.right :
      Subgroup (MulAut B)) ≤ n) (d : MulAut B) : FactorsThrough β d := by
  obtain ⟨r, hr, l, hl, hd⟩ := large_subgroup_product
    (extensionSubgroup β.right) (extensionSubgroup β.left) n hn hg
    hright hleft (by simpa only [inf_comm] using hinter) d
  refine ⟨l, r.symm, hl, (extensionSubgroup β.right).inv_mem hr, ?_⟩
  simpa only [MulEquiv.symm_symm, MulAut.mul_def] using hd

/-- Removing a twist is equivalent to belonging to the restriction product. -/
theorem factorsThrough_iff_nonempty_iso (β : RankTwoAmalgam L B R) (d : MulAut B) :
    FactorsThrough β d ↔ Nonempty (Iso (twistRight β d) β) := by
  constructor
  · exact fun h => ⟨h.iso⟩
  · rintro ⟨e⟩
    refine ⟨e.middle, d.symm.trans e.middle, ⟨e.left, e.left_commutes⟩, ?_, ?_⟩
    · refine ⟨e.right, fun b => ?_⟩
      simpa only [twistRight, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, MulEquiv.trans_apply] using e.right_commutes (d.symm b)
    · ext b
      simp

/-- Transport a twist through an isomorphism of both inclusion squares. -/
def Iso.twistRight {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : Iso α β) (d : MulAut B) :
    Iso (RankTwoAmalgam.twistRight α d)
      (RankTwoAmalgam.twistRight β ((MulAut.congr e.middle) d)) where
  left := e.left
  middle := e.middle
  right := e.right
  left_commutes := e.left_commutes
  right_commutes b := by
    simpa only [RankTwoAmalgam.twistRight, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using e.right_commutes (d b)

/-- The restriction-product obstruction is independent of a compatible model marking. -/
theorem Iso.factorsThrough_iff {α : RankTwoAmalgam L B R}
    {β : RankTwoAmalgam L' B' R'} (e : Iso α β) (d : MulAut B) :
    FactorsThrough α d ↔ FactorsThrough β ((MulAut.congr e.middle) d) := by
  rw [factorsThrough_iff_nonempty_iso, factorsThrough_iff_nonempty_iso]
  constructor
  · rintro ⟨f⟩
    exact ⟨(e.twistRight d).symm.trans (f.trans e)⟩
  · rintro ⟨f⟩
    exact ⟨(e.twistRight d).trans (f.trans e.symm)⟩

/-- Unconditional factorization needs no additional faithfulness premise. -/
theorem iso_of_twist_factorization {p : ℕ} [Fact p.Prime]
    [Finite L'] [Finite R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (hα : SylowEmbedded p α) (hβ : SylowEmbedded p β)
    (e : ParabolicEquiv α β) (hfactor : ∀ d : MulAut B', FactorsThrough β d) :
    Nonempty (Iso α β) := by
  obtain ⟨d, ⟨f⟩⟩ := exists_twist_iso hα hβ e
  exact ⟨f.trans (hfactor d).iso⟩

end Theory.GroupTheory.RankTwoAmalgam
