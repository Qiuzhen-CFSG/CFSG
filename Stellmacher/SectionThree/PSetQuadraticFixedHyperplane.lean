module
public import Stellmacher.SectionOne.FixedSylowGenerationCore
public import Stellmacher.SectionOne.QuadraticSubgroupFixedHyperplane
public import Stellmacher.SectionThree.PSetIrreducibleHyperplaneActor

/-!
# A quadratic fixed hyperplane inside the original local actor

For an actual action of a solvable PSet member on a finite elementary binary
module, kill its native two-core and assume that a supplied Sylow image's
fixed space generates the module. Every quadratic subgroup of that Sylow
has a subgroup of index at most two whose fixed space escapes a prescribed
proper module subgroup. The output is a subgroup of the original actor.

Pass to the literal automorphism range. Fixed generation and faithfulness
kill its two-core; a nontrivial Sylow image gives even order. The proved
local residual theorem provides the odd-core supplement required for the
hereditary form of (1.2). Pull the returned subgroup back inside the supplied
actor, preserving relative index and the exact image fixed space. A trivial
actor image is handled directly without an even-order assumption.

Source: Stellmacher (1.2), as used in (8.6), printed p.42, source-(5), with
local odd-residual input from (3.3). This is an action bridge, independent
of the Section Eight graph or classification alternatives.
-/

namespace Stellmacher.SectionThree
open SectionOne
universe u v

public theorem pSet_quadratic_fixed_hyperplane_lift
    {G : Type u} {V : Type v} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V]
    (S P : Subgroup G) (h : Hypotheses G S)
    (hP : P ∈ PSet (⊤ : Subgroup G) S) (hsolv : Group.IsSolvable P)
    (action : P →* MulAut V) (hker : pCore 2 P ≤ action.ker)
    (T : Sylow 2 P)
    (hgen : (⊤ : Subgroup V) = actionClosure action.range V
      (FixedPoints.subgroup ((T : Subgroup P).map action.rangeRestrict) V))
    (Y : Subgroup P) (hYT : Y ≤ (T : Subgroup P))
    (hquad : IsQuadraticAction (Y.map action.rangeRestrict) V)
    (R : Subgroup V) (hR : R ≠ ⊤) :
    ∃ Y₀ : Subgroup P, Y₀ ≤ Y ∧ Nat.card Y ≤ 2 * Nat.card Y₀ ∧
      ¬ FixedPoints.subgroup (Y₀.map action.rangeRestrict) V ≤ R := by
  classical
  let X := action.range
  let q := action.rangeRestrict
  let Tbar := T.mapSurjective action.rangeRestrict_surjective
  let Ybar := Y.map q
  have hYTbar : Ybar ≤ (Tbar : Subgroup X) := Subgroup.map_mono hYT
  have hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro actor hactor
    apply Subtype.ext
    apply MulEquiv.ext
    intro vector
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor vector (Set.mem_univ vector)
  have hcore : pCore 2 X = ⊥ := twoCore_eq_bot_of_fixed_sylow_generation Tbar hfaith hgen
  by_cases hY : Ybar = ⊥
  · refine ⟨Y, le_rfl, by omega, ?_⟩
    intro hfixed
    apply hR
    apply top_unique
    intro vector _
    apply hfixed
    intro actor
    have hone : (actor : X) = 1 := hY.le actor.property
    change (actor : X) • vector = vector
    rw [hone, one_smul]
  have hTne : (Tbar : Subgroup X) ≠ ⊥ := fun heq => hY (bot_unique (hYTbar.trans_eq heq))
  let _ : Nontrivial Tbar := (Subgroup.nontrivial_iff_ne_bot _).mpr hTne
  have heven : Even (Nat.card X) := by
    obtain ⟨exponent, hpositive, hcard⟩ := Tbar.isPGroup'.nontrivial_iff_card.mp inferInstance
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card Tbar by rw [hcard]; exact dvd_pow_self 2 (by omega)).trans
    exact Subgroup.card_subgroup_dvd_card _
  let _ : Group.IsSolvable P := hsolv
  have hsetup : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective action.rangeRestrict_surjective, heven, hfaith, hcore⟩
  have hkerq : pCore 2 P ≤ q.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hsupp := pSet_surjective_odd_supplement S P h hP hsolv q
    action.rangeRestrict_surjective hkerq Tbar
  obtain ⟨Y₁, hY₁, hcard, hescape⟩ :=
    exists_fixed_hyperplane_of_quadratic_subgroup hsetup Tbar hsupp hgen
      Ybar hYTbar hquad R hR
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
  have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup P) Y₀ Y bot_le hY₀
  simp only [Subgroup.relIndex_bot_left] at hcountbar hcount
  have hpos : 0 < Nat.card Y₁ := Nat.card_pos
  have hbound : Y₁.relIndex Ybar ≤ 2 := by nlinarith
  rw [hrel] at hcount
  refine ⟨Y₀, hY₀, by nlinarith, ?_⟩
  change ¬ FixedPoints.subgroup (Y₀.map q) V ≤ R
  rw [himage]
  exact hescape

end Stellmacher.SectionThree
