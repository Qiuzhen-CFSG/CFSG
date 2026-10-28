module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.LiftDefect
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CenterControl
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
import Mathlib.Tactic.Group

/-!
# Counting centralizers using the actual lifting defect

Let P be the preimage in I of the centralizer of the projective image of w.
Every fiber of the central commutator P → Z(L) is a right coset of C_I(w).
Consequently |P| = |image(defect)| |C_I(w)|, while projective descent gives
|P| = 4 |C_standard(w-bar)|. This uses no centralizer-lifting surjectivity.

If C_I(w) induces the full automorphism group of Z(L), one nonidentity defect
propagates by conjugation to all three nonidentity central elements. The two
factors of four then cancel. The same center action has kernel C_C_I(w)(Z(L))
and image of order six, giving the second centralizer count.

These are transfer and counting results. Establishing the projective bound,
full center action, and a nonidentity defect for the marked cover remains a
model calculation; none is assumed as a property of the cover.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. The central four is the actual Z(L), with its original inclusion.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

omit [L.Normal] in
/-- The kernel centralizing hypothesis puts the entire covering center in C_I(w). -/
theorem centralFour_le_centralizer (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I)) :
    (center L).map L.subtype ≤ centralizerIn w := by
  intro z hz
  exact mem_centralizer_singleton_iff.mpr (hw z hz)

/-- Restriction to C_I(w) preserves the actual center of L. -/
noncomputable def centralFourEquiv (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I)) :
    centralFourIn (L := L) w ≃* center L :=
  (subgroupOfEquivOfLe (centralFour_le_centralizer w hw)).trans
    ((center L).equivMapOfInjective L.subtype L.subtype_injective).symm

/-- The restricted covering center has order four, not merely order dividing four. -/
theorem centralFour_card (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I)) :
    Nat.card (centralFourIn (L := L) w) = 4 := by
  rw [Nat.card_congr (centralFourEquiv w hw).toEquiv]
  let := d.cover.center_isKleinFour
  exact IsKleinFour.card_four

/-- The whole Klein four survives inside the chosen centralizer. -/
theorem centralFour_isKleinFour (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I)) :
    IsKleinFour (centralFourIn (L := L) w) where
  card_four := centralFour_card d w hw
  exponent_two := by
    rw [Monoid.exponent_eq_of_mulEquiv (centralFourEquiv w hw)]
    exact d.cover.center_isKleinFour.exponent_two

omit [L.Normal] in
/-- The relative centralizer is precisely the restriction of C_I(Z(L)). -/
theorem centerCentralizer_eq_comap (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I)) :
    centerCentralizerIn (L := L) w =
      (centralizer ((center L).map L.subtype : Set I)).comap (centralizerIn w).subtype := by
  ext x
  constructor
  · intro hx z hz
    exact congrArg Subtype.val (hx ⟨z, centralFour_le_centralizer w hw hz⟩ hz)
  · intro hx z hz
    exact Subtype.ext (hx z.val hz)

/-- Actual conjugation on the covering center, restricted to C_I(w). -/
@[expose] def centralFourAction (d : Overgroup L) (w : I) :
    centralizerIn w →* MulAut (centralFourIn (L := L) w) := by
  let := centralFourIn_normal d w
  exact MulAut.conjNormal

/-- The kernel of this action is the relative centralizer appearing in the source. -/
theorem centralFourAction_ker (d : Overgroup L) (w : I) :
    (centralFourAction d w).ker = centerCentralizerIn (L := L) w := by
  ext x
  constructor
  · intro hx z hz
    have h := congrArg (fun a : MulAut (centralFourIn (L := L) w) =>
      (a ⟨z, hz⟩ : centralizerIn w)) hx
    change x * z * x⁻¹ = z at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hx
    change centralFourAction d w x = 1
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change x * (z : centralizerIn w) * x⁻¹ = z
    rw [← hx z z.property, mul_inv_cancel_right]

/-- Count the centralizer using its actual action on the central four. -/
theorem centralizer_card_eq_centerCentralizer_mul_image (d : Overgroup L) (w : I) :
    Nat.card (centralizerIn w) = Nat.card (centerCentralizerIn (L := L) w) *
      Nat.card (centralFourAction d w).range := by
  rw [card_eq_card_quotient_mul_card_subgroup (centralFourAction d w).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (centralFourAction d w)).toEquiv,
    centralFourAction_ker, Nat.mul_comm]

/-- Full action on the central four has image order six. -/
theorem centralFourAction_image_card_of_surjective (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (ha : Function.Surjective (centralFourAction d w)) :
    Nat.card (centralFourAction d w).range = 6 := by
  rw [(centralFourAction d w).range_eq_top_of_surjective ha,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (MulAut _)) ≃* _).toEquiv]
  let := centralFour_isKleinFour d w hw
  exact IsKleinFour.card_mulAut _

/-- A full center action turns the bound 864 into the bound 144. -/
theorem centerCentralizer_card_dvd_of_action_surjective (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (ha : Function.Surjective (centralFourAction d w))
    (hc : Nat.card (centralizerIn w) ∣ 864) :
    Nat.card (centerCentralizerIn (L := L) w) ∣ 144 := by
  rw [centralizer_card_eq_centerCentralizer_mul_image d w,
    centralFourAction_image_card_of_surjective d w hw ha] at hc
  exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 6)).mp hc

/-- Actual commutation implies projective commutation. -/
theorem centralizer_le_preimage (d : Overgroup L) (w : I) :
    centralizerIn w ≤ projectiveCentralizerPreimage d w := by
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg (projectiveAction L d.cover)
    (mem_centralizer_singleton_iff.mp hx)

/-- Equal defects characterize a right coset of the actual centralizer. -/
theorem liftDefect_eq_iff (d : Overgroup L) (w : I)
    (x y : projectiveCentralizerPreimage d w) :
    centralizerLiftDefect d w x = centralizerLiftDefect d w y ↔
      (y : I)⁻¹ * (x : I) ∈ centralizerIn w := by
  rw [Subtype.ext_iff, centralizerLiftDefect_val, centralizerLiftDefect_val, centralizerIn,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun z : I => (y : I)⁻¹ * z * w * (x : I)) h
    convert h' using 1 <;> group
  · intro h
    have h' := congrArg (fun z : I => (y : I) * z * (x : I)⁻¹ * w⁻¹) h
    convert h' using 1 <;> group

/-- Conjugation by C_I(w) acts on defect values by the actual action on Z(L). -/
theorem liftDefect_conj (d : Overgroup L) (w : I)
    (c : centralizerIn w) (x : projectiveCentralizerPreimage d w) :
    (centralizerLiftDefect d w
      (⟨c, centralizer_le_preimage d w c.property⟩ * x *
        (⟨c, centralizer_le_preimage d w c.property⟩ : projectiveCentralizerPreimage d w)⁻¹) : I) =
      (c : I) * (centralizerLiftDefect d w x : I) * (c : I)⁻¹ := by
  have hc : (MulAut.conj (c : I)) w = w := by
    change (c : I) * w * (c : I)⁻¹ = w
    rw [mem_centralizer_singleton_iff.mp c.property, mul_inv_cancel_right]
  simp only [centralizerLiftDefect_val]
  change (MulAut.conj (c : I) (x : I)) * w *
    (MulAut.conj (c : I) (x : I))⁻¹ * w⁻¹ =
    MulAut.conj (c : I) ((x : I) * w * (x : I)⁻¹ * w⁻¹)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]

/-- Full center action propagates any nonidentity defect to all four values. -/
theorem defect_surjective_of_nontrivial (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (ha : Function.Surjective (centralFourAction d w))
    (hx : ∃ x, centralizerLiftDefect d w x ≠ 1) :
    Function.Surjective (centralizerLiftDefect d w) := by
  classical
  let := centralFour_isKleinFour d w hw
  obtain ⟨x, hx⟩ := hx
  let j : (center L).map L.subtype → centralFourIn (L := L) w := fun z =>
    ⟨⟨z, centralFour_le_centralizer w hw z.property⟩, z.property⟩
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : centralFourIn (L := L) w => z.val.val) h)
  have hj1 : j 1 = 1 := rfl
  intro z
  by_cases hz : z = 1
  · refine ⟨1, ?_⟩
    rw [hz]
    apply Subtype.ext
    simp [centralizerLiftDefect_val]
  · let a := j (centralizerLiftDefect d w x)
    let b := j z
    have ha1 : a ≠ 1 := by
      intro h
      exact hx (hj (h.trans hj1.symm))
    have hb1 : b ≠ 1 := by
      intro h
      exact hz (hj (h.trans hj1.symm))
    let u : MulAut (centralFourIn (L := L) w) := IsKleinFour.mulEquiv
      (Equiv.swap a b) (Equiv.swap_apply_of_ne_of_ne (Ne.symm ha1) (Ne.symm hb1))
    obtain ⟨c, hc⟩ := ha u
    refine ⟨⟨c, centralizer_le_preimage d w c.property⟩ * x *
      (⟨c, centralizer_le_preimage d w c.property⟩ : projectiveCentralizerPreimage d w)⁻¹, ?_⟩
    apply Subtype.ext
    rw [liftDefect_conj]
    have h := congrArg (fun v : MulAut (centralFourIn (L := L) w) => (v a).val.val) hc
    exact h.trans (congrArg (fun t : centralFourIn (L := L) w => t.val.val)
      (Equiv.swap_apply_left a b))

private noncomputable def defectFiberEquiv (d : Overgroup L) (w : I)
    (y : projectiveCentralizerPreimage d w) :
    {x : projectiveCentralizerPreimage d w //
      centralizerLiftDefect d w x = centralizerLiftDefect d w y} ≃ centralizerIn w where
  toFun x := ⟨(y : I)⁻¹ * x.val, (liftDefect_eq_iff d w x.val y).mp x.property⟩
  invFun c := ⟨y * ⟨c, centralizer_le_preimage d w c.property⟩, by
    apply (liftDefect_eq_iff d w _ y).mpr
    simpa only [coe_mul, inv_mul_cancel_left] using c.property⟩
  left_inv x := by ext; simp
  right_inv c := by ext; simp

private noncomputable def defectDecomposition (d : Overgroup L) (w : I) :
    projectiveCentralizerPreimage d w ≃
      Set.range (centralizerLiftDefect d w) × centralizerIn w := by
  classical
  let f := centralizerLiftDefect d w
  let g : projectiveCentralizerPreimage d w → Set.range f := fun x => ⟨f x, x, rfl⟩
  refine (Equiv.sigmaFiberEquiv g).symm.trans ?_
  refine (Equiv.sigmaCongrRight fun z => ?_).trans (Equiv.sigmaEquivProd _ _)
  let y := Classical.choose z.property
  have hy : f y = z.val := Classical.choose_spec z.property
  exact (Equiv.subtypeEquivRight (fun x => by
    change (⟨f x, _⟩ : Set.range f) = z ↔ f x = f y
    rw [Subtype.ext_iff, hy])).trans (defectFiberEquiv d w y)

/-- Every nonempty defect fiber is a coset of C_I(w), even though the defect
is only a crossed homomorphism. -/
theorem preimage_card_eq_defect_mul_centralizer (d : Overgroup L) (w : I) :
    Nat.card (projectiveCentralizerPreimage d w) =
      Nat.card (Set.range (centralizerLiftDefect d w)) * Nat.card (centralizerIn w) := by
  rw [Nat.card_congr (defectDecomposition d w), Nat.card_prod]

/-- Projective descent has its full central kernel on the preimage centralizer. -/
theorem preimage_card_eq_four_mul_projectiveCentralizer (d : Overgroup L) (w : I) :
    Nat.card (projectiveCentralizerPreimage d w) = 4 * Nat.card (projectiveCentralizer d w) := by
  let f := (projectiveAction L d.cover).comp (projectiveCentralizerPreimage d w).subtype
  have hk : (projectiveAction L d.cover).ker ≤ projectiveCentralizerPreimage d w := by
    intro x hx
    change projectiveAction L d.cover x ∈ centralizer _
    rw [show projectiveAction L d.cover x = 1 from hx]
    exact one_mem _
  have hker : Nat.card f.ker = 4 := by
    change Nat.card ((projectiveAction L d.cover).ker.subgroupOf
      (projectiveCentralizerPreimage d w)) = 4
    rw [Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv]
    exact projectiveAction_ker_card d
  have hr : f.range = projectiveCentralizer d w := by
    rw [MonoidHom.range_comp, range_subtype]
    exact projectiveCentralizerPreimage_map d w
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker, hr, Nat.mul_comm]

/-- Four defect values exactly cancel the fourfold kernel in the order calculation.
This cardinal equality does not assert surjectivity of centralizer descent. -/
theorem centralizer_card_eq_projective_of_defect_surjective (d : Overgroup L) (w : I)
    (hs : Function.Surjective (centralizerLiftDefect d w)) :
    Nat.card (centralizerIn w) = Nat.card (projectiveCentralizer d w) := by
  have h := (preimage_card_eq_defect_mul_centralizer d w).symm.trans
    (preimage_card_eq_four_mul_projectiveCentralizer d w)
  have hc : Nat.card (Set.range (centralizerLiftDefect d w)) = 4 := by
    rw [Set.range_eq_univ.mpr hs, Nat.card_univ,
      card_map_of_injective L.subtype_injective]
    let := d.cover.center_isKleinFour
    exact IsKleinFour.card_four
  rw [hc] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

/-- A nonidentity defect gives an explicit projective centralizer element that
has no lift in the actual centralizer. -/
theorem centralizerImage_proper_of_nontrivial_defect (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (hx : ∃ x, centralizerLiftDefect d w x ≠ 1) :
    ∃ a ∈ projectiveCentralizer d w,
      a ∉ (centralizerIn w).map (projectiveAction L d.cover) := by
  obtain ⟨x, hx⟩ := hx
  refine ⟨projectiveAction L d.cover x, ?_, ?_⟩
  · rw [← projectiveCentralizerPreimage_map]
    exact mem_map_of_mem _ x.property
  · intro ha
    exact hx ((projective_mem_centralizerImage_iff d w hw x).mp ha)

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
