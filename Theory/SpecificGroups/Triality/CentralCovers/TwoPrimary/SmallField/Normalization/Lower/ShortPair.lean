module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.ShortPair.Upper
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.ShortPair.Algebra

/-!
# The torus-normalized short–short exchange at q = 2

Compare the actual commutator with the full prescribed correction word.
The genuine base exchange puts their difference in the central kernel.
The two exact upper trace relations make this difference additive in each
parameter. Arms-torus equivariance and injectivity on the correction subgroup
make it invariant under simultaneous nonzero GF(8) scalars. The elementary
scalar-pairing argument then kills the defect.

This proves the short–short input to
`SmallField.exists_lowerNormalized_of_torus_calculations`, retaining precisely
arms normalization, commuting pairs and upper relations. The final export
applies it to the literal collector pair `(0,2)`.

Sources: GLS3 §2.4.5(b)(4), with the actual D₄ marking, and §6.1;
Aschbacher–Smith A.2.4 and I.1.3 (PDF pp.44 and 418).
-/

set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
open RootSections RootSections.ShortPolynomial ShortPair
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
open scoped commutatorElement
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "K" => ExtensionField P
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
variable {E : Type*} [Group E] {f : E →* G}

private theorem conjugate_mul (z x y : E) :
    z*(x*y)*z⁻¹ = (z*x*z⁻¹)*(z*y*z⁻¹) := by group

private theorem conjugate_inv (z x : E) :
    z*x⁻¹*z⁻¹ = (z*x*z⁻¹)⁻¹ := by group

private theorem correction_project (L : RootSections 1 Nat.zero_lt_one f) (s t : K) :
    f ⁅L.shortValue 0 s, L.shortValue 1 t⁆ = f (correction L s t) := by
  have h : f (L.shortValue 0 s) * f (L.shortValue 1 t) =
      f (L.shortValue 1 t) * f (L.shortValue 0 s) * f (correction L s t) := by
    simpa only [correction, shortValue, longValue, map_mul, L.project_short,
      L.project_long, mul_assoc] using short_zero_one_exchange P rfl s t
  calc
    _ = f ((L.shortValue 1 t * L.shortValue 0 s)⁻¹ *
        (L.shortValue 0 s * L.shortValue 1 t)) := by
      congr 1
      simp only [commutatorElement_def, mul_inv_rev, short_inv, mul_assoc]
    _ = _ := by rw [map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel_left]

private def defect (L : RootSections 1 Nat.zero_lt_one f) (s t : K) : E :=
  (correction L s t)⁻¹ * ⁅L.shortValue 0 s, L.shortValue 1 t⁆

private theorem defect_central (L : RootSections 1 Nat.zero_lt_one f)
    (hk : f.ker ≤ Subgroup.center E) (s t : K) : defect L s t ∈ Subgroup.center E := by
  apply hk
  simp only [MonoidHom.mem_ker, defect, map_mul, map_inv, correction_project, inv_mul_cancel]

private theorem left_difference (L : RootSections 1 Nat.zero_lt_one f) (s t : K) :
    (L.shortValue 0 s * correction L s t)⁻¹ *
      (L.shortValue 1 t * L.shortValue 0 s * (L.shortValue 1 t)⁻¹) = defect L s t := by
  simp only [defect, mul_inv_rev, commutatorElement_def, short_inv, mul_assoc]

private theorem right_difference (L : RootSections 1 Nat.zero_lt_one f)
    (hk : f.ker ≤ Subgroup.center E) (hC : L.CommutingRelations) (s t : K) :
    (L.shortValue 1 t * correction L s t)⁻¹ *
      (L.shortValue 0 s * L.shortValue 1 t * (L.shortValue 0 s)⁻¹) = (defect L s t)⁻¹ := by
  have hd : Commute (correction L s t) (defect L s t) :=
    Subgroup.mem_center_iff.mp (defect_central L hk s t) _
  have hc : Commute (correction L s t) ⁅L.shortValue 0 s, L.shortValue 1 t⁆ := by
    simpa only [defect, mul_inv_cancel_left] using (Commute.refl (correction L s t)).mul_right hd
  calc
    _ = (correction L s t)⁻¹ * ⁅L.shortValue 1 t, L.shortValue 0 s⁆ := by
      simp only [mul_inv_rev, commutatorElement_def, short_inv, mul_assoc]
    _ = ⁅L.shortValue 0 s, L.shortValue 1 t⁆⁻¹ * correction L s t := by
      rw [← commutatorElement_inv, correction_inv L hC]
      exact hc.inv_right.eq
    _ = _ := by simp only [defect, mul_inv_rev, inv_inv]

private theorem defect_left_add (L : RootSections 1 Nat.zero_lt_one f)
    (hk : f.ker ≤ Subgroup.center E) (hc : CommutingPairs L) (hu : UpperRelations L)
    (s u t : K) : defect L (s+u) t = defect L s t * defect L u t := by
  have ha := candidate_left_add L (commutingRelations L hc) (upper_trace L hc hu 0) t
  have hb (s u : K) :
      L.shortValue 1 t * L.shortValue 0 (s+u) * (L.shortValue 1 t)⁻¹ =
      (L.shortValue 1 t * L.shortValue 0 s * (L.shortValue 1 t)⁻¹) *
        (L.shortValue 1 t * L.shortValue 0 u * (L.shortValue 1 t)⁻¹) := by
    rw [ShortPolynomial.short_add, conjugate_mul]
  have he := difference_add
    (fun s => L.shortValue 0 s * correction L s t)
    (fun s => L.shortValue 1 t * L.shortValue 0 s * (L.shortValue 1 t)⁻¹) ha hb (by
    intro x
    rw [left_difference]
    exact defect_central L hk x t) s u
  simpa only [left_difference] using he

private theorem defect_inv (L : RootSections 1 Nat.zero_lt_one f)
    (hk : f.ker ≤ Subgroup.center E) (hc : CommutingPairs L) (hu : UpperRelations L)
    (s t : K) : (defect L s t)⁻¹ = defect L s t := by
  have h := defect_left_add L hk hc hu s s t
  have hz : defect L 0 t = 1 := by
    simp [defect, correction, shortValue, longValue, higherCoefficient, -fieldFrobenius_apply]
  rw [CharTwo.add_self_eq_zero, hz] at h
  exact inv_eq_of_mul_eq_one_left h.symm

private theorem defect_right_add (L : RootSections 1 Nat.zero_lt_one f)
    (hk : f.ker ≤ Subgroup.center E) (hc : CommutingPairs L) (hu : UpperRelations L)
    (s t u : K) : defect L s (t+u) = defect L s t * defect L s u := by
  have hC := commutingRelations L hc
  have ha := candidate_right_add L hC (upper_trace L hc hu 1) s
  have hb (t u : K) :
      L.shortValue 0 s * L.shortValue 1 (t+u) * (L.shortValue 0 s)⁻¹ =
      (L.shortValue 0 s * L.shortValue 1 t * (L.shortValue 0 s)⁻¹) *
        (L.shortValue 0 s * L.shortValue 1 u * (L.shortValue 0 s)⁻¹) := by
    rw [ShortPolynomial.short_add, conjugate_mul]
  have he := difference_add
    (fun t => L.shortValue 1 t * correction L s t)
    (fun t => L.shortValue 0 s * L.shortValue 1 t * (L.shortValue 0 s)⁻¹) ha hb (by
    intro x
    rw [right_difference L hk hC]
    exact (Subgroup.center E).inv_mem (defect_central L hk s x)) t u
  simpa only [right_difference L hk hC, defect_inv L hk hc hu] using he

private theorem correction_conjugate (L : RootSections 1 Nat.zero_lt_one f)
    (hT : ArmsTorusNormalized L) (hc : CommutingPairs L)
    (a : Kˣ) (z : E) (hz : f z = torusActor P rfl .arms a) (s t : K) :
    z * correction L s t * z⁻¹ = correction L (a.val^2*s) (a.val^2*t) := by
  have hC := commutingRelations L hc
  have hs (i : Fin 3) (s : K) :
      z * L.shortValue i s * z⁻¹ = L.shortValue i (shortWeight a i*s) := hT.1 a z hz i s
  have hl (i : Fin 3) (s : fixedField P) :
      z * L.longValue i s * z⁻¹ = L.longValue i s := hT.2 a z hz i s
  apply eq_of_tail L hC
  · simp only [correction, conjugate_mul, hs, hl]
    exact tail_mem L hC _ _ _
  · exact tail_mem L hC _ _ _
  · calc
      _ = f (z * ⁅L.shortValue 0 s, L.shortValue 1 t⁆ * z⁻¹) := by
        simp only [map_mul, map_inv, correction_project]
      _ = f ⁅L.shortValue 0 (a.val^2*s), L.shortValue 1 (a.val^2*t)⁆ := by
        rw [conjugate_commutatorElement, hs, hs]
        rfl
      _ = _ := correction_project L _ _

private theorem defect_scaling (L : RootSections 1 Nat.zero_lt_one f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hT : ArmsTorusNormalized L) (hc : CommutingPairs L) (c : K) (hc0 : c ≠ 0)
    (s t : K) : defect L (c*s) (c*t) = defect L s t := by
  let a : Kˣ := Units.mk0 c hc0 ^ 4
  have ha : a.val ^ 2 = c := by
    have h := pow_card_eq_one' (x := Units.mk0 c hc0)
    rw [Nat.card_units, card_extensionField] at h
    change (Units.mk0 c hc0)^7 = 1 at h
    have hv := congrArg Units.val h
    change c^7 = 1 at hv
    change (c^4)^2 = c
    rw [← pow_mul]
    calc
      c^8 = c^7*c := pow_succ c 7
      _ = c := by rw [hv, one_mul]
  obtain ⟨z, hz⟩ := hf (torusActor P rfl .arms a)
  have hs (i : Fin 3) (s : K) : z*L.shortValue i s*z⁻¹ =
      L.shortValue i (shortWeight a i*s) := hT.1 a z hz i s
  have he : z * defect L s t * z⁻¹ = defect L (c*s) (c*t) := by
    simp only [defect, conjugate_mul, conjugate_inv, conjugate_commutatorElement,
      correction_conjugate L hT hc a z hz, hs, shortWeight,
      Matrix.cons_val_zero, Matrix.cons_val_one, ha]
  rw [← he, Subgroup.mem_center_iff.mp (defect_central L hk s t) z,
    mul_inv_cancel_right]

/-- The two upper trace exchanges and arms normalization remove the central
short–short defect in any surjective central extension of the genuine carrier. -/
theorem shortPairRelation_of_central_armsTorusNormalized
    (L : RootSections 1 Nat.zero_lt_one f) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (hT : ArmsTorusNormalized L)
    (hc : CommutingPairs L) (hu : UpperRelations L) : ShortPairRelation L := by
  intro s t
  have hd : defect L s t = 1 := invariant_pairing_eq_one
    (by rw [card_extensionField]; decide : 4 < Nat.card K) (defect L)
    (defect_left_add L hk hc hu) (defect_right_add L hk hc hu)
    (defect_scaling L hf hk hT hc) s t
  have he : ⁅L.shortValue 0 s, L.shortValue 1 t⁆ = correction L s t := by
    exact (inv_mul_eq_one.mp hd).symm
  change L.shortValue 0 s * L.shortValue 1 t = _
  calc
    _ = (L.shortValue 1 t * L.shortValue 0 s) *
        ⁅L.shortValue 0 s, L.shortValue 1 t⁆ := by
      simp only [commutatorElement_def, short_inv]
      have hx : L.shortValue 0 s * L.shortValue 0 s = 1 := by
        rw [← ShortPolynomial.short_add, CharTwo.add_self_eq_zero]
        exact (L.shortRoot 0).map_one
      have hy : L.shortValue 1 t * L.shortValue 1 t = 1 := by
        rw [← ShortPolynomial.short_add, CharTwo.add_self_eq_zero]
        exact (L.shortRoot 1).map_one
      simp only [mul_assoc, ← mul_assoc (L.shortValue 0 s) (L.shortValue 0 s), hx,
        one_mul, ← mul_assoc (L.shortValue 1 t) (L.shortValue 1 t), hy]
    _ = _ := by rw [he]; simp only [correction, shortValue, longValue, mul_assoc]

/-- The exact short–short relation used by the lower-normalization assembly. -/
theorem shortPairRelation_of_armsTorusNormalized
    (M : RootSections 1 Nat.zero_lt_one (PerfectCentralCovering.universalProjection G))
    (hT : ArmsTorusNormalized M) (hc : CommutingPairs M) (hu : UpperRelations M) :
    ShortPairRelation M :=
  shortPairRelation_of_central_armsTorusNormalized M
    (PerfectCentralCovering.universalProjection_surjective G)
    (PerfectCentralCovering.universalProjection_ker_le_center G) hT hc hu

/-- The short–short calculation discharges precisely the `(0,2)` collector pair. -/
theorem shortPairExchange_of_armsTorusNormalized
    (M : RootSections 1 Nat.zero_lt_one (PerfectCentralCovering.universalProjection G))
    (hT : ArmsTorusNormalized M) (hc : CommutingPairs M) (hu : UpperRelations M) :
    PairExchange M 0 2 :=
  (shortPairRelation_of_armsTorusNormalized M hT hc hu).pairExchange
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
