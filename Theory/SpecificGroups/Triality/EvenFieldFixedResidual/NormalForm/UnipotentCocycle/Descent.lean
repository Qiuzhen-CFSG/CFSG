module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.RootAction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Descending split-positive cocycle solutions to genuine triality

A nonempty solution set for u = v⁻¹ c(v) is a torsor for the c-fixed subgroup.
In a finite two-group it therefore has two-power cardinality. A commuting
order-three automorphism fixing u acts on this set and must fix a solution.

Apply this to the split positive subgroup and the actual graph-field defining
twist. The faithful `carrierToSplit` map then transports a fixed solution into
the original descended unipotent subgroup. The coefficient map and the
orientation of the coboundary are preserved literally. This reduction needs
only split-positive cocycle solvability; it avoids separate trace calculations
in the six folded coordinates. It does not prove that remaining split input.

Sources: GLS3 §§2.1, 2.3–2.5, `refs/KGroup/GLS3/chapter2.tex`, for the fixed-point
construction and field convention; Aschbacher–Smith 16.1.3–4, printed p.1171,
`refs/quasithin.pdf`. The carrier naturality proof follows the existing private
calculation in `StandardTwoRank/FourSemilinear/HighestRoot.lean`.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm.UnipotentCocycle
open OuterOdd Parabolics ConcreteBruhat.FixedDescent PositiveCoordinates

private def solutionEquiv {G : Type*} [Group G] (c : MulAut G)
    (u v : G) (hv : u = v⁻¹ * c v) :
    c.fixedSubgroup ≃ {w : G // u = w⁻¹ * c w} where
  toFun k := ⟨k.val * v, by
    rw [map_mul, (MulAut.mem_fixedSubgroup c k.val).mp k.property, mul_inv_rev]
    simpa only [mul_assoc, inv_mul_cancel_left] using hv⟩
  invFun w := ⟨w.val * v⁻¹, by
    apply (MulAut.mem_fixedSubgroup c _).mpr
    have hw : c w.val = w.val * u := by
      calc
        c w.val = w.val * (w.val⁻¹ * c w.val) := by group
        _ = w.val * u := congrArg (w.val * ·) w.property.symm
    have hv' : c v = v * u := by rw [hv]; group
    rw [map_mul, map_inv, hw, hv']
    group⟩
  left_inv k := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

private theorem exists_fixed_solution {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (c d : MulAut G) (hcd : Commute c d)
    (hd : d ^ 3 = 1) (u : G) (hu : d u = u)
    (hsol : ∃ v : G, u = v⁻¹ * c v) :
    ∃ v : G, d v = v ∧ u = v⁻¹ * c v := by
  obtain ⟨v, hv⟩ := hsol
  let S := {w : G // u = w⁻¹ * c w}
  have hmem (w : S) : u = (d w.val)⁻¹ * c (d w.val) := by
    have hw := congrArg d w.property
    rw [hu, map_mul, map_inv] at hw
    exact hw.trans (congrArg ((d w.val)⁻¹ * ·) (DFunLike.congr_fun hcd.eq w.val).symm)
  let f : S → S := fun w => ⟨d w.val, hmem w⟩
  have hf : ∀ w, f (f (f w)) = w := by
    intro w
    apply Subtype.ext
    exact DFunLike.congr_fun hd w.val
  let e : Equiv.Perm S :=
    { toFun := f
      invFun := fun w => f (f w)
      left_inv := hf
      right_inv := hf }
  have he : e ^ 3 = 1 := by
    apply Equiv.ext
    intro w
    exact hf w
  have hA : IsPGroup 3 (Subgroup.zpowers e) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one he
  have hcard : ¬ 3 ∣ Nat.card S := by
    rw [← Nat.card_congr (solutionEquiv c u v hv)]
    obtain ⟨k, hk⟩ := (hG.to_subgroup c.fixedSubgroup).exists_card_eq
    rw [hk]
    intro hh
    have hh' := Nat.prime_three.dvd_of_dvd_pow hh
    omega
  obtain ⟨w, hw⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  exact ⟨w.val, congrArg Subtype.val (hw ⟨e, Subgroup.mem_zpowers e⟩), w.property⟩

/-- The faithful carrier map intertwines the original quotient action with split coefficient action. -/
theorem carrierToSplit_coefficient (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (g : Carrier P) :
    carrierToSplit P hp (coefficientAction P e g) =
      coefficientSplit P e (carrierToSplit P hp g) := by
  obtain ⟨x, hx⟩ := toCarrier_surjective P g
  rw [← hx]
  calc
    _ = carrierToSplit P hp (toCarrier P (coefficientElementary P e x)) :=
      congrArg (carrierToSplit P hp) (coefficientCarrier_toCarrier P e x)
    _ = elementaryInclusion P (coefficientElementary P e x) := carrierToSplit_toCarrier P hp _
    _ = coefficientSplit P e (elementaryInclusion P x) := rfl
    _ = _ := congrArg (coefficientSplit P e) (carrierToSplit_toCarrier P hp x).symm

/-- A split-positive solution descends to the genuine triality unipotent subgroup.
The graph-field fixed solution is obtained by the order-three action on the solution torsor. -/
theorem unipotent_cocycle_of_splitPositive
    (n : ℕ) (hn : 0 < n) (e : CoefficientAut (binaryParameters n hn))
    (hsol : ∀ u : SplitGroup (binaryParameters n hn),
      u ∈ positiveSubgroup (binaryParameters n hn) → u * coefficientSplit _ e u = 1 →
      ∃ v : SplitGroup (binaryParameters n hn), v ∈ positiveSubgroup (binaryParameters n hn) ∧
        u = v⁻¹ * coefficientSplit _ e v)
    (u : BinaryCarrier n hn) (hu : u ∈ unipotent (binaryParameters n hn))
    (huc : u * coefficientAction _ e u = 1) :
    ∃ v : BinaryCarrier n hn, v ∈ unipotent (binaryParameters n hn) ∧
      u = v⁻¹ * coefficientAction _ e v := by
  let P := binaryParameters n hn
  let U := positiveSubgroup P
  let c : MulAut U := restrictCoefficientSubgroup (coefficientSplit P e) U
    (coefficientSplit_positiveSubgroup P e)
  let d : MulAut U := restrictCoefficientSubgroup (graphFieldAutomorphism P) U
    (positiveSubgroup_invariant P)
  let x : U := ⟨carrierToSplit P rfl u, (mem_descend_iff P rfl _ u).mp hu⟩
  have hcd : Commute c d := by
    apply MulEquiv.ext
    intro y
    exact Subtype.ext (coefficientSplit_graphField P e y.val).symm
  have hd : d ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    exact Subtype.ext (graphFieldAutomorphism_three P y.val)
  have hdx : d x = x := Subtype.ext (carrierToSplit_mem_fixed P rfl u)
  have hxc : x.val * coefficientSplit P e x.val = 1 := by
    calc
      _ = carrierToSplit P rfl (u * coefficientAction P e u) :=
        ((carrierToSplit P rfl).map_mul _ _ |>.trans
          (congrArg (carrierToSplit P rfl u * ·)
            (carrierToSplit_coefficient P rfl e u))).symm
      _ = 1 := (congrArg (carrierToSplit P rfl) huc).trans (map_one _)
  obtain ⟨y, hyU, hxy⟩ := hsol x.val x.property hxc
  have hxy' : x = (⟨y, hyU⟩ : U)⁻¹ * c ⟨y, hyU⟩ := Subtype.ext hxy
  obtain ⟨v, hdv, hv⟩ := exists_fixed_solution
    (isPGroup_positiveSubgroup_binary n hn) c d hcd hd x hdx ⟨⟨y, hyU⟩, hxy'⟩
  obtain ⟨w, hw⟩ := exists_carrier_of_fixed P rfl v.val (congrArg Subtype.val hdv)
  refine ⟨w, (mem_descend_iff P rfl _ w).mpr ?_, ?_⟩
  · rw [hw]
    exact v.property
  · apply carrierToSplit_injective P rfl
    calc
      _ = v.val⁻¹ * coefficientSplit P e v.val := congrArg Subtype.val hv
      _ = (carrierToSplit P rfl w)⁻¹ *
          coefficientSplit P e (carrierToSplit P rfl w) := by rw [hw]
      _ = carrierToSplit P rfl (w⁻¹ * coefficientAction P e w) :=
        ((carrierToSplit P rfl).map_mul _ _ |>.trans
          (congrArg₂ (· * ·) ((carrierToSplit P rfl).map_inv w)
            (carrierToSplit_coefficient P rfl e w))).symm
end Triality.Standard.EvenField.NormalForm.UnipotentCocycle
