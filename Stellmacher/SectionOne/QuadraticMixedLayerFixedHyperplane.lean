module
public import Stellmacher.SectionOne.FixedSylowGenerationCore
public import Stellmacher.SectionOne.QuadraticSubgroupFixedHyperplane

/-!
# Quadratic fixed hyperplanes through a mixed normal layer

Let a finite solvable group act on a finite elementary binary module.
Suppose normal subgroups R≤L have R a two-group and L/R of odd order,
and L together with a supplied Sylow two-subgroup S generates the group.
If the S-image fixed space generates the module, every subgroup Y≤S with
quadratic image has a subgroup of index at most two whose image fixed
space escapes any prescribed proper module subgroup.

Pass to the literal automorphism range. Faithful fixed-Sylow generation
kills its two-core and hence the image of R. The image of L has order
dividing [L:R], so it lies in the range's odd core and supplies the odd-core
supplement. Apply the hereditary form of (1.2), then pull its subgroup back
inside Y; the relative index and exact image fixed space are preserved.
A trivial Y-image is handled directly without assuming the range is even.

This is the mixed-layer use of Stellmacher (1.2) in (10.1)(a3)(9), Journal
of Algebra 190 (1997), printed pp.61–62. Relative index expresses the odd
layer without introducing a quotient action or a quotient normality instance.
-/

namespace Stellmacher.SectionOne
universe u v

/-- Lift an index-at-most-two subgroup whose image fixed space escapes a proper module subgroup. -/
public theorem quadratic_fixed_hyperplane_lift_of_mixed_layer
    {K : Type u} {V : Type v} [Group K] [Finite K] [Group.IsSolvable K]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (action : K →* MulAut V) (R L : Subgroup K) [R.Normal] [L.Normal]
    (hR2 : IsPGroup 2 R) (hRL : R ≤ L) (hodd : Nat.Coprime 2 (R.relIndex L))
    (S : Sylow 2 K) (hsupp : (⊤ : Subgroup K) = L ⊔ (S : Subgroup K))
    (hgen : (⊤ : Subgroup V) = actionClosure action.range V
      (FixedPoints.subgroup ((S : Subgroup K).map action.rangeRestrict) V))
    (Y : Subgroup K) (hYS : Y ≤ (S : Subgroup K))
    (hquad : IsQuadraticAction (Y.map action.rangeRestrict) V)
    (D : Subgroup V) (hD : D ≠ ⊤) :
    ∃ Y₀ : Subgroup K, Y₀ ≤ Y ∧ Nat.card Y ≤ 2 * Nat.card Y₀ ∧
      ¬ FixedPoints.subgroup (Y₀.map action.rangeRestrict) V ≤ D := by
  classical
  let X := action.range
  let q := action.rangeRestrict
  let Sbar := S.mapSurjective action.rangeRestrict_surjective
  let Ybar := Y.map q
  have hYSbar : Ybar ≤ (Sbar : Subgroup X) := Subgroup.map_mono hYS
  have hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro actor hactor
    apply Subtype.ext
    apply MulEquiv.ext
    intro vector
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor vector (Set.mem_univ vector)
  have hcore : pCore 2 X = ⊥ :=
    twoCore_eq_bot_of_fixed_sylow_generation Sbar hfaith hgen
  by_cases hY : Ybar = ⊥
  · refine ⟨Y, le_rfl, by omega, ?_⟩
    intro hfixed
    apply hD
    apply top_unique
    intro vector _
    apply hfixed
    intro actor
    have hone : (actor : X) = 1 := hY.le actor.property
    change (actor : X) • vector = vector
    rw [hone, one_smul]
  have hSne : (Sbar : Subgroup X) ≠ ⊥ :=
    fun heq => hY (bot_unique (hYSbar.trans_eq heq))
  let _ : Nontrivial Sbar := (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  have heven : Even (Nat.card X) := by
    obtain ⟨exponent, hpositive, hcard⟩ := Sbar.isPGroup'.nontrivial_iff_card.mp inferInstance
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card Sbar by rw [hcard]; exact dvd_pow_self 2 (by omega)).trans
    exact Subgroup.card_subgroup_dvd_card _
  have hsetup : Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective action.rangeRestrict_surjective, heven, hfaith, hcore⟩
  have hRimage : R.map q ≤ pCore 2 X :=
    le_sSup ⟨(inferInstance : R.Normal).map q action.rangeRestrict_surjective, hR2.map q⟩
  have hRker : R ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := R)).mp
      (bot_unique (hRimage.trans_eq hcore))
  have hdiv : Nat.card (L.map q) ∣ R.relIndex L := by
    rw [← Subgroup.relIndex_ker]
    have h := Subgroup.relIndex_dvd_of_le_left L (le_inf hRL hRker)
    rwa [Subgroup.inf_relIndex_left] at h
  have hLodd : Nat.Coprime 2 (Nat.card (L.map q)) := hodd.of_dvd_right hdiv
  have hLcore : L.map q ≤ oddCore X :=
    le_sSup ⟨(inferInstance : L.Normal).map q action.rangeRestrict_surjective, hLodd⟩
  have hsuppX : (⊤ : Subgroup X) = oddCore X ⊔ (Sbar : Subgroup X) := by
    apply le_antisymm ?_ le_top
    have h := congrArg (fun U : Subgroup K => U.map q) hsupp
    rw [Subgroup.map_top_of_surjective q action.rangeRestrict_surjective,
      Subgroup.map_sup] at h
    exact h.le.trans (sup_le_sup hLcore le_rfl)
  obtain ⟨Y₁, hY₁, hcard, hescape⟩ :=
    exists_fixed_hyperplane_of_quadratic_subgroup hsetup Sbar hsuppX hgen
      Ybar hYSbar hquad D hD
  let Y₀ := Y ⊓ Y₁.comap q
  have hY₀ : Y₀ ≤ Y := inf_le_left
  have himage : Y₀.map q = Y₁ := by
    apply le_antisymm
    · rintro image ⟨actor, hactor, rfl⟩
      exact hactor.2
    · intro image himage
      obtain ⟨actor, hactor, heq⟩ := hY₁ himage
      exact ⟨actor, ⟨hactor, show q actor ∈ Y₁ from heq.symm ▸ himage⟩, heq⟩
  have hrel : Y₀.relIndex Y = Y₁.relIndex Ybar := by
    change (Y ⊓ Y₁.comap q).relIndex Y = _
    rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
  have hcountbar := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup X) Y₁ Ybar bot_le hY₁
  have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup K) Y₀ Y bot_le hY₀
  simp only [Subgroup.relIndex_bot_left] at hcountbar hcount
  have hpos : 0 < Nat.card Y₁ := Nat.card_pos
  have hbound : Y₁.relIndex Ybar ≤ 2 := by nlinarith
  rw [hrel] at hcount
  refine ⟨Y₀, hY₀, by nlinarith, ?_⟩
  change ¬ FixedPoints.subgroup (Y₀.map q) V ≤ D
  rw [himage]
  exact hescape

end Stellmacher.SectionOne
