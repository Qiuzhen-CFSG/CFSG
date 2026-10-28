module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.LayerCoordinateEquivalence
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.nonsingular_coefficient
public import Theory.AlgebraicGroup.RootData.RelativeWeyl

/-!
# Upper relative-root commutator detection

This module proves the elementwise detection needed to identify the reversed
relative-root filtration with the upper central series.  If an element of the
unipotent radical first survives in the adjacent quotient at height `i`, the
direct-product coordinate equivalence selects a nonzero exact-height root
coordinate.  The root-extension theorem supplies a height-one root whose sum
with that root has height `i + 1`.  The Chevalley commutator formula then shows
that the selected output coordinate is a nonzero structure constant times the
input coordinate, while all other input coordinates and all higher terms
vanish in the adjacent quotient.

The nonsingular-characteristic hypothesis makes that structure constant
nonzero.  The classified invalid-rank cases are not treated as irreducible:
the exported Dynkin dichotomy reduces them to a diagonal Cartan matrix, where
every root is a signed base root and hence has relative height at most one.
Thus the positive-height-below-maximum situation required by root extension
forces the genuine irreducible branch.

This is the elementwise upper-series step in the relative-root form of GLS3,
Chapter 1, Lemma 1.13.6.  Its coordinate model comes from the filtered
Chevalley collection and exact-layer independence APIs.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma layer_le_first
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    S.layer i ≤ S.layer 1 := by
  letI := Fintype.ofFinite S.ι
  exact relativeRootSeries_antitone S.D S.rootEquiv S.base.support
    S.coeff S.J hi

omit [IsAlgClosed k] in
private lemma layer_commutator_le_two_steps
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    ⁅S.layer i, S.layer (i + 1)⁆ ≤ S.layer (i + 2) := by
  letI := Fintype.ofFinite S.ι
  calc
    ⁅S.layer i, S.layer (i + 1)⁆ = ⁅S.layer (i + 1), S.layer i⁆ :=
      Subgroup.commutator_comm _ _
    _ ≤ ⁅S.layer (i + 1), S.layer 1⁆ :=
      Subgroup.commutator_mono le_rfl (layer_le_first S i hi)
    _ ≤ S.layer (i + 2) := by
      simpa only [ParabolicRelativeRootSetup.layer, ← S.rootBase_support,
        Nat.add_assoc] using
        relativeRootSeries_commutator_series_le S.D S.C S.rootPairing
          S.rootEquiv S.rootBase S.coeff S.rootSimpleRootExpansion
          S.chevalleySystem S.J (i + 1) (by omega)

private def fixedLayerCommutatorValue
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi :0 < i)
    (y : S.layer 1) (a : S.layer i) : S.layer (i + 1) :=
  ⟨⁅(a : Variety.Point K), (y : Variety.Point K)⁆, by
    letI := Fintype.ofFinite S.ι
    have hComm : ⁅S.layer i, S.layer 1⁆ ≤ S.layer (i + 1) := by
      simpa only [ParabolicRelativeRootSetup.layer, ← S.rootBase_support] using
        relativeRootSeries_commutator_series_le S.D S.C S.rootPairing
          S.rootEquiv S.rootBase S.coeff S.rootSimpleRootExpansion
          S.chevalleySystem S.J i hi
    exact hComm (Subgroup.commutator_mem_commutator a.2 y.2)⟩

private noncomputable def fixedLayerCommutatorHom
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (y : S.layer 1) :
    let hN := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
    letI := hN
    S.layer i →*
      (S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) := by
  letI := Fintype.ofFinite S.ι
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  letI := parabolicRelativeRootLayer_quotient_commutative S (i + 1) (by omega)
  let hDeep : ⁅S.layer i, S.layer (i + 1)⁆ ≤ S.layer (i + 2) :=
    layer_commutator_le_two_steps S i hi
  let hNext : S.layer (i + 2) ≤ S.layer (i + 1) :=
    parabolicRelativeRootLayer_succ_le S (i + 1)
  let commInNext (a : S.layer i) : S.layer (i + 1) :=
    fixedLayerCommutatorValue S i hi y a
  refine
    { toFun := fun a => QuotientGroup.mk'
        ((S.layer (i + 2)).subgroupOf (S.layer (i + 1))) (commInNext a)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        change ⁅((1 : S.layer i) : Variety.Point K),
          (y : Variety.Point K)⁆ ∈ S.layer (i + 2)
        simp
      map_mul' := ?_ }
  intro a b
  let z : S.layer (i + 1) := commInNext b
  let w : S.layer (i + 1) := commInNext a
  have hazDeep : ⁅(a : Variety.Point K), (z : Variety.Point K)⁆ ∈
      S.layer (i + 2) :=
    hDeep (Subgroup.commutator_mem_commutator a.2 z.2)
  have hconjMem : (a : Variety.Point K) * (z : Variety.Point K) *
      (a : Variety.Point K)⁻¹ ∈ S.layer (i + 1) := by
    rw [show (a : Variety.Point K) * (z : Variety.Point K) *
        (a : Variety.Point K)⁻¹ =
        ⁅(a : Variety.Point K), (z : Variety.Point K)⁆ * z by
      exact conj_eq_commutatorElement_mul]
    exact (S.layer (i + 1)).mul_mem (hNext hazDeep) z.2
  let zConj : S.layer (i + 1) :=
    ⟨(a : Variety.Point K) * (z : Variety.Point K) *
      (a : Variety.Point K)⁻¹, hconjMem⟩
  have hzConj : (zConj :
      S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) = z := by
    rw [QuotientGroup.eq_iff_div_mem]
    show ((zConj / z : S.layer (i + 1)) : Variety.Point K) ∈
      S.layer (i + 2)
    simpa [zConj, div_eq_mul_inv, commutatorElement_def] using hazDeep
  change (commInNext (a * b) :
      S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) =
    (w : S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) * z
  have hcommMul : commInNext (a * b) = zConj * w := by
    apply Subtype.ext
    exact commutatorElement_mul_left_eq_conj_mul _ _ _
  rw [hcommMul]
  change (zConj :
      S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) * w = w * z
  rw [hzConj]
  exact mul_comm' _ _

private noncomputable def fixedLayerQuotientCommutatorHom
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (y : S.layer 1) :
    let hSource := parabolicRelativeRootLayer_next_normal S i hi
    letI := hSource
    let hTarget := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
    letI := hTarget
    (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) →*
      (S.layer (i + 1) ⧸
        (S.layer (i + 2)).subgroupOf (S.layer (i + 1))) := by
  letI := Fintype.ofFinite S.ι
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  let f := fixedLayerCommutatorHom S i hi y
  apply QuotientGroup.lift
    ((S.layer (i + 1)).subgroupOf (S.layer i)) f
  intro a ha
  apply (QuotientGroup.eq_one_iff _).2
  show ⁅(a : Variety.Point K), (y : Variety.Point K)⁆ ∈
    S.layer (i + 2)
  have hComm : ⁅S.layer (i + 1), S.layer 1⁆ ≤ S.layer (i + 2) := by
    simpa only [ParabolicRelativeRootSetup.layer, ← S.rootBase_support,
      Nat.add_assoc] using
      relativeRootSeries_commutator_series_le S.D S.C S.rootPairing
        S.rootEquiv S.rootBase S.coeff S.rootSimpleRootExpansion
        S.chevalleySystem S.J (i + 1) (by omega)
  exact hComm (Subgroup.commutator_mem_commutator ha y.2)

omit [IsAlgClosed k] in
private theorem fixedLayerQuotientCommutatorHom_mk
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (y : S.layer 1) (a : S.layer i) :
    let hSource := parabolicRelativeRootLayer_next_normal S i hi
    letI := hSource
    let hTarget := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
    letI := hTarget
    fixedLayerQuotientCommutatorHom S i hi y
        (QuotientGroup.mk'
          ((S.layer (i + 1)).subgroupOf (S.layer i)) a) =
      QuotientGroup.mk'
        ((S.layer (i + 2)).subgroupOf (S.layer (i + 1)))
        (fixedLayerCommutatorValue S i hi y a) := by
  rfl

private noncomputable def fixedLayerCoordinateCommutatorHom
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (y : S.layer 1) :
    Multiplicative (S.layerRootIndex i → k) →*
      Multiplicative (S.layerRootIndex (i + 1) → k) := by
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  exact (parabolicRelativeRootLayer_quotientCoordinateEquiv S (i + 1) (by omega)).toMonoidHom.comp
    ((fixedLayerQuotientCommutatorHom S i hi y).comp
      (parabolicRelativeRootLayer_coordinateHom S i hi))

private def multiplicativeEval
    {I : Type*} (alpha : I) :
    Multiplicative (I → k) →* Multiplicative k where
  toFun f := Multiplicative.ofAdd ((Multiplicative.toAdd f) alpha)
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def layerQuotientCoordinateAt
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) :
    letI := parabolicRelativeRootLayer_next_normal S i hi
    (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) →*
      Multiplicative k := by
  letI := parabolicRelativeRootLayer_next_normal S i hi
  exact (multiplicativeEval alpha).comp
    (parabolicRelativeRootLayer_quotientCoordinateEquiv S i hi).toMonoidHom

private theorem layerQuotientCoordinateAt_root
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha gamma : S.layerRootIndex i) (t : k) :
    letI := parabolicRelativeRootLayer_next_normal S i hi
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    layerQuotientCoordinateAt S i hi alpha
        (QuotientGroup.mk'
          ((S.layer (i + 1)).subgroupOf (S.layer i))
          (S.layerRootElement i gamma t)) =
      Multiplicative.ofAdd
        ((Pi.single gamma t : S.layerRootIndex i → k) alpha) := by
  classical
  letI := parabolicRelativeRootLayer_next_normal S i hi
  change (parabolicRelativeRootLayer_quotientCoordinateEquiv S i hi
      (QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        (S.layerRootElement i gamma t)) : S.layerRootIndex i → k) alpha = _
  rw [parabolicRelativeRootLayer_quotientCoordinateEquiv_root]
  rfl

private theorem layerQuotientCoordinateAt_deep
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (z : S.layer i)
    (hz : (z : Variety.Point K) ∈ S.layer (i + 1)) :
    letI := parabolicRelativeRootLayer_next_normal S i hi
    layerQuotientCoordinateAt S i hi alpha
        (QuotientGroup.mk'
          ((S.layer (i + 1)).subgroupOf (S.layer i)) z) = 1 := by
  letI := parabolicRelativeRootLayer_next_normal S i hi
  rw [show (QuotientGroup.mk'
      ((S.layer (i + 1)).subgroupOf (S.layer i)) z) = 1 by
    apply (QuotientGroup.eq_one_iff _).2
    exact hz]
  simp

private theorem fixedLayerQuotientCommutatorHom_root
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (beta : S.layerRootIndex 1)
    (delta : S.layerRootIndex (i + 1))
    (hroot : S.rootPairing.root (S.rootEquiv delta.1) =
      S.rootPairing.root (S.rootEquiv alpha.1) +
        S.rootPairing.root (S.rootEquiv beta.1)) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      let hSource := parabolicRelativeRootLayer_next_normal S i hi
      letI := hSource
      let hTarget := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
      letI := hTarget
      fixedLayerQuotientCommutatorHom S i hi
          (S.layerRootElement 1 beta 1)
          (QuotientGroup.mk'
            ((S.layer (i + 1)).subgroupOf (S.layer i))
            (S.layerRootElement i alpha t)) =
        QuotientGroup.mk'
          ((S.layer (i + 2)).subgroupOf (S.layer (i + 1)))
          (S.layerRootElement (i + 1) delta (c * t)) := by
  classical
  letI := Fintype.ofFinite S.ι
  let hlin : LinearIndependent ℚ
      ![S.rootPairing.root (S.rootEquiv alpha.1),
        S.rootPairing.root (S.rootEquiv beta.1)] := by
    apply S.rootPairing.linearIndependent_of_add_mem_range_root'
    rw [← hroot]
    exact ⟨S.rootEquiv delta.1, rfl⟩
  have hLI : AreLinearlyIndependentRoots S.D S.rootPairing S.rootEquiv
      alpha.1 beta.1 := by
    simpa [AreLinearlyIndependentRoots] using
      (LinearIndependent.pair_iff.mp hlin)
  let q : ChevalleyCommutatorTerm S.D.Root := ⟨1, 1, delta.1⟩
  have hqsum : q.i + q.j = 2 := by simp [q]
  have hqvalid : IsValidChevalleyCommutatorTerm S.D S.rootPairing
      S.rootEquiv alpha.1 beta.1 q := by
    refine ⟨by simp [q], by simp [q], ?_⟩
    simpa [q] using hroot
  rcases S.chevalleySystem.2.2.2.2.1 alpha.1 beta.1 hLI with
    ⟨order, coefficient, hnodup, hpairwise, hvalid, hexpected, hformula⟩
  have hqorder : q ∈ order := (hvalid q).mpr hqvalid
  have horderHead : ∃ tail, order = q :: tail := by
    induction order with
    | nil => simp at hqorder
    | cons p l ih =>
      by_cases hpq : p = q
      · exact ⟨l, by simp [hpq]⟩
      · have hqtail : q ∈ l :=
          (List.mem_cons.mp hqorder).resolve_left (Ne.symm hpq)
        have hpvalid := (hvalid p).mp (by simp)
        have hpi : 0 < p.i := hpvalid.1
        have hpj : 0 < p.j := hpvalid.2.1
        have hpdeg : 2 ≤ p.i + p.j := by omega
        have hpqdeg : p.i + p.j ≤ q.i + q.j :=
          (List.pairwise_cons.mp hpairwise).1 q hqtail
        have hpdegEq : p.i + p.j = q.i + q.j := by omega
        have hp_i : p.i = 1 := by
          have hsum : p.i + p.j = 2 := by rw [hpdegEq, hqsum]
          omega
        have hp_j : p.j = 1 := by
          have hsum : p.i + p.j = 2 := by rw [hpdegEq, hqsum]
          omega
        have hproot : p.root = delta.1 := by
          apply S.rootEquiv.injective
          apply S.rootPairing.root.injective
          rw [hpvalid.2.2, hqvalid.2.2]
          simp [hp_i, hp_j, q]
        have hpqeq : p = q := by
          cases p
          simp_all [q]
        exact (hpq hpqeq).elim
  obtain ⟨tail, rfl⟩ := horderHead
  have htailStrict : ∀ r ∈ tail, q.i + q.j < r.i + r.j := by
    intro r hr
    have hqr := (List.pairwise_cons.mp hpairwise).1 r hr
    by_contra hnot
    have hrdEq : r.i + r.j = q.i + q.j :=
      Nat.le_antisymm (Nat.le_of_not_gt hnot) hqr
    have hrvalid := (hvalid r).mp (by simp [hr])
    have hriPos : 0 < r.i := hrvalid.1
    have hrjPos : 0 < r.j := hrvalid.2.1
    have hri : r.i = 1 := by
      have hsum : r.i + r.j = 2 := by simpa [q] using hrdEq
      omega
    have hrj : r.j = 1 := by
      have hsum : r.i + r.j = 2 := by simpa [q] using hrdEq
      omega
    have hrroot : r.root = delta.1 := by
      apply S.rootEquiv.injective
      apply S.rootPairing.root.injective
      rw [hrvalid.2.2, hqvalid.2.2]
      simp [hri, hrj, q]
    have hreq : r = q := by
      cases r
      simp_all [q]
    exact (List.nodup_cons.mp hnodup).1 (by simpa [hreq] using hr)
  have htailMem : ∀ r ∈ tail, ∀ s : k, S.C.x r.root s ∈ S.layer (i + 2) := by
    intro r hr s
    have hrvalid := (hvalid r).mp (by simp [hr])
    have hrheight := relativeRootHeight_of_validChevalleyCommutatorTerm
      S.D S.rootPairing S.rootEquiv S.rootBase
        (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion r hrvalid
    have hrh : (i + 2 : ℤ) ≤ RelativeRootHeight S.coeff S.rootBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv r.root) := by
      have hri : (1 : ℤ) ≤ r.i := by
        exact_mod_cast (Nat.succ_le_of_lt hrvalid.1)
      have hrj : (1 : ℤ) ≤ r.j := by
        exact_mod_cast (Nat.succ_le_of_lt hrvalid.2.1)
      have hdeg : 3 ≤ r.i + r.j := by
        have := htailStrict r hr
        omega
      rw [hrheight]
      have hAlpha : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv alpha.1) = i := by
        simpa only [S.rootBase_support] using alpha.2
      have hBeta : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv beta.1) = (1 : ℤ) := by
        simpa only [S.rootBase_support, Nat.cast_one] using beta.2
      rw [hAlpha, hBeta]
      nlinarith
    rw [ParabolicRelativeRootSetup.layer, ← S.rootBase_support,
      RelativeRootSeries, RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨r.root, hrh, by
      rw [← (S.chevalleySystem.1 r.root).2]
      exact Set.mem_range_self _⟩
  have hc : coefficient q ≠ 0 :=
    S.expectedChevalleyCoefficient_ne_zero classification hType hNonsingular
      (hexpected q (by simp))
  refine ⟨coefficient q, hc, ?_⟩
  intro t
  let tailProduct : Variety.Point K :=
    ChevalleyCommutatorTermWordProduct S.C
      (tail.map fun r => (r,
        coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j))
  have htailProduct : tailProduct ∈ S.layer (i + 2) := by
    apply Subgroup.list_prod_mem
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨z, hz, rfl⟩
    rw [List.mem_map] at hz
    rcases hz with ⟨r, hr, rfl⟩
    exact htailMem r hr _
  have hzeroAlpha : S.C.x alpha.1 0 = 1 := by
    simpa using (S.chevalleySystem.2.2.2.1 alpha.1 0 0)
  have hzeroBeta : S.C.x beta.1 0 = 1 := by
    simpa using (S.chevalleySystem.2.2.2.1 beta.1 0 0)
  have hxinv : S.C.x alpha.1 (-t) = (S.C.x alpha.1 t)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [S.chevalleySystem.2.2.2.1 alpha.1 (-t) t]
    simpa using hzeroAlpha
  have hyinv : S.C.x beta.1 (-1) = (S.C.x beta.1 1)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [S.chevalleySystem.2.2.2.1 beta.1 (-1) 1]
    simpa using hzeroBeta
  have hformula' := hformula (-t) (-1)
  simp only [List.map_cons, List.prod_cons] at hformula'
  have hcomm : ⁅(S.C.x alpha.1 t), (S.C.x beta.1 1)⁆ =
      S.C.x delta.1 (coefficient q * t) * tailProduct := by
    simpa [q, tailProduct, ChevalleyCommutatorTermWordProduct,
      List.map_map, Function.comp_def, hxinv, hyinv,
      commutatorElement_def, mul_assoc] using hformula'
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  let hNext : S.layer (i + 2) ≤ S.layer (i + 1) :=
    parabolicRelativeRootLayer_succ_le S (i + 1)
  let alphaLayer : S.layer i := S.layerRootElement i alpha t
  let betaLayer : S.layer 1 := S.layerRootElement 1 beta 1
  let commNext : S.layer (i + 1) :=
    fixedLayerCommutatorValue S i hi betaLayer alphaLayer
  let headNext : S.layer (i + 1) := S.layerRootElement (i + 1) delta (coefficient q * t)
  let tailNext : S.layer (i + 1) := ⟨tailProduct, hNext htailProduct⟩
  have hcommNext : commNext = headNext * tailNext := by
    apply Subtype.ext
    change ⁅(alphaLayer : Variety.Point K), (betaLayer : Variety.Point K)⁆ =
      (headNext : Variety.Point K) * tailProduct
    rw [show (alphaLayer : Variety.Point K) = S.C.x alpha.1 t by
        exact S.layerRootElement_value i alpha t,
      show (betaLayer : Variety.Point K) = S.C.x beta.1 1 by
        exact S.layerRootElement_value 1 beta 1,
      show (headNext : Variety.Point K) =
          S.C.x delta.1 (coefficient q * t) by
        exact S.layerRootElement_value (i + 1) delta (coefficient q * t)]
    exact hcomm
  dsimp only
  rw [fixedLayerQuotientCommutatorHom_mk]
  change (commNext : (S.layer (i + 1) ⧸
      (S.layer (i + 2)).subgroupOf (S.layer (i + 1)))) =
    (headNext : (S.layer (i + 1) ⧸
      (S.layer (i + 2)).subgroupOf (S.layer (i + 1))))
  rw [hcommNext]
  change (headNext : (S.layer (i + 1) ⧸
      (S.layer (i + 2)).subgroupOf (S.layer (i + 1)))) *
    (tailNext : (S.layer (i + 1) ⧸
      (S.layer (i + 2)).subgroupOf (S.layer (i + 1)))) = headNext
  rw [show (tailNext : (S.layer (i + 1) ⧸
      (S.layer (i + 2)).subgroupOf (S.layer (i + 1)))) = 1 by
    apply (QuotientGroup.eq_one_iff _).2
    exact htailProduct]
  simp

private theorem fixedLayerCoordinateCommutatorHom_root
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (beta : S.layerRootIndex 1)
    (delta : S.layerRootIndex (i + 1))
    (hroot : S.rootPairing.root (S.rootEquiv delta.1) =
      S.rootPairing.root (S.rootEquiv alpha.1) +
        S.rootPairing.root (S.rootEquiv beta.1)) :
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    letI : DecidableEq (S.layerRootIndex (i + 1)) := Classical.decEq _
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      fixedLayerCoordinateCommutatorHom S i hi
          (S.layerRootElement 1 beta 1)
          (Multiplicative.ofAdd (Pi.single alpha t)) =
        Multiplicative.ofAdd (Pi.single delta (c * t)) := by
  classical
  obtain ⟨c, hc, hquotient⟩ := fixedLayerQuotientCommutatorHom_root
    S classification hType hNonsingular i hi alpha beta delta hroot
  refine ⟨c, hc, ?_⟩
  intro t
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  change parabolicRelativeRootLayer_quotientCoordinateEquiv S (i + 1) (by omega)
      (fixedLayerQuotientCommutatorHom S i hi
        (S.layerRootElement 1 beta 1)
        (parabolicRelativeRootLayer_coordinateHom S i hi
          (Multiplicative.ofAdd (Pi.single alpha t)))) = _
  rw [parabolicRelativeRootLayer_coordinateHom_single]
  rw [hquotient t]
  exact parabolicRelativeRootLayer_quotientCoordinateEquiv_root
    S (i + 1) (by omega) delta (c * t)

private theorem fixedLayerCoordinateCommutatorHom_root_at_of_ne
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (i : ℕ) (hi : 0 < i)
    (alpha gamma : S.layerRootIndex i) (beta : S.layerRootIndex 1)
    (delta : S.layerRootIndex (i + 1))
    (hroot : S.rootPairing.root (S.rootEquiv delta.1) =
      S.rootPairing.root (S.rootEquiv alpha.1) +
        S.rootPairing.root (S.rootEquiv beta.1))
    (hgamma : gamma ≠ alpha) (t : k) :
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    multiplicativeEval delta
      (fixedLayerCoordinateCommutatorHom S i hi
        (S.layerRootElement 1 beta 1)
        (Multiplicative.ofAdd (Pi.single gamma t))) = 1 := by
  classical
  letI := Fintype.ofFinite S.ι
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  let hNext : S.layer (i + 2) ≤ S.layer (i + 1) :=
    parabolicRelativeRootLayer_succ_le S (i + 1)
  let gammaLayer : S.layer i := S.layerRootElement i gamma t
  let betaLayer : S.layer 1 := S.layerRootElement 1 beta 1
  let commNext : S.layer (i + 1) :=
    fixedLayerCommutatorValue S i hi betaLayer gammaLayer
  change layerQuotientCoordinateAt S (i + 1) (by omega) delta
      (fixedLayerQuotientCommutatorHom S i hi
        (S.layerRootElement 1 beta 1)
        (parabolicRelativeRootLayer_coordinateHom S i hi
          (Multiplicative.ofAdd (Pi.single gamma t)))) = 1
  rw [parabolicRelativeRootLayer_coordinateHom_single]
  rw [fixedLayerQuotientCommutatorHom_mk]
  change layerQuotientCoordinateAt S (i + 1) (by omega) delta
      (QuotientGroup.mk'
        ((S.layer (i + 2)).subgroupOf (S.layer (i + 1))) commNext) = 1
  by_cases hsame : gamma.1 = beta.1
  · have hcommOne : ⁅S.C.x gamma.1 t, S.C.x beta.1 1⁆ = 1 := by
      rw [hsame]
      apply Commute.commutator_eq
      show S.C.x beta.1 t * S.C.x beta.1 1 =
        S.C.x beta.1 1 * S.C.x beta.1 t
      rw [S.chevalleySystem.2.2.2.1 beta.1 t 1,
        S.chevalleySystem.2.2.2.1 beta.1 1 t]
      congr 1
      exact add_comm _ _
    have : commNext = 1 := by
      apply Subtype.ext
      change ⁅(gammaLayer : Variety.Point K), (betaLayer : Variety.Point K)⁆ = 1
      rw [show (gammaLayer : Variety.Point K) = S.C.x gamma.1 t by
          exact S.layerRootElement_value i gamma t,
        show (betaLayer : Variety.Point K) = S.C.x beta.1 1 by
          exact S.layerRootElement_value 1 beta 1]
      exact hcommOne
    rw [this]
    simp
  · have hGammaPos : S.rootBase.IsPos (S.rootEquiv gamma.1) := by
      apply base_isPos_of_relativeRootHeight_pos S.rootPairing S.rootBase
        (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion
      have hg : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv gamma.1) = (i : ℤ) := by
        simpa only [S.rootBase_support] using gamma.2
      rw [hg]
      exact_mod_cast hi
    have hBetaPos : S.rootBase.IsPos (S.rootEquiv beta.1) := by
      apply base_isPos_of_relativeRootHeight_pos S.rootPairing S.rootBase
        (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion
      have hb : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv beta.1) = (1 : ℤ) := by
        simpa only [S.rootBase_support, Nat.cast_one] using beta.2
      rw [hb]
      norm_num
    let := S.rootPairing.indexNeg
    have hnotopp : S.rootPairing.root (S.rootEquiv gamma.1) ≠
        -S.rootPairing.root (S.rootEquiv beta.1) := by
      intro hneg
      have hidx := S.rootPairing.root_eq_neg_iff.mp hneg
      have hGammaNeg : S.rootBase.IsPos (-S.rootEquiv beta.1) := by
        simpa [hidx] using hGammaPos
      exact ((RootPairing.Base.IsPos.neg_iff_not
        (P := S.rootPairing) (b := S.rootBase)
        (i := S.rootEquiv beta.1)).mp hGammaNeg) hBetaPos
    have hne : S.rootEquiv gamma.1 ≠ S.rootEquiv beta.1 := by
      intro h
      apply hsame
      exact S.rootEquiv.injective h
    have hlin := RootPairing.IsReduced.linearIndependent
      (P := S.rootPairing) hne hnotopp
    rw [LinearIndependent.pair_iff] at hlin
    have hLI : AreLinearlyIndependentRoots S.D S.rootPairing S.rootEquiv
        gamma.1 beta.1 := by
      simpa [AreLinearlyIndependentRoots] using hlin
    rcases S.chevalleySystem.2.2.2.2.1 gamma.1 beta.1 hLI with
      ⟨order, coefficient, _hnodup, _hpairwise, hvalid, _hexpected, hformula⟩
    have htermMem (r : ChevalleyCommutatorTerm S.D.Root) (hr : r ∈ order) :
        S.C.x r.root (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j) ∈
          S.layer (i + 1) := by
      have hrvalid := (hvalid r).mp hr
      have hrheight := relativeRootHeight_of_validChevalleyCommutatorTerm
        S.D S.rootPairing S.rootEquiv S.rootBase
          (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion r hrvalid
      rw [ParabolicRelativeRootSetup.layer, ← S.rootBase_support,
        RelativeRootSeries, RootSubgroupGenerated]
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨r.root, ?_, ?_⟩
      · rw [hrheight]
        have hGamma : RelativeRootHeight S.coeff S.rootBase.support
            (S.rootEquiv '' S.J) (S.rootEquiv gamma.1) = (i : ℤ) := by
          simpa only [S.rootBase_support] using gamma.2
        have hBeta : RelativeRootHeight S.coeff S.rootBase.support
            (S.rootEquiv '' S.J) (S.rootEquiv beta.1) = (1 : ℤ) := by
          simpa only [S.rootBase_support, Nat.cast_one] using beta.2
        rw [hGamma, hBeta]
        have hri : (1 : ℤ) ≤ r.i := by
          exact_mod_cast (Nat.succ_le_of_lt hrvalid.1)
        have hrj : (1 : ℤ) ≤ r.j := by
          exact_mod_cast (Nat.succ_le_of_lt hrvalid.2.1)
        have hiZ : (1 : ℤ) ≤ i := by exact_mod_cast hi
        change (i : ℤ) + 1 ≤ (r.i : ℤ) * (i : ℤ) + (r.j : ℤ) * 1
        nlinarith
      · rw [← (S.chevalleySystem.1 r.root).2]
        exact Set.mem_range_self _
    have hterm (r : ChevalleyCommutatorTerm S.D.Root) (hr : r ∈ order) :
        layerQuotientCoordinateAt S (i + 1) (by omega) delta
          (QuotientGroup.mk'
            ((S.layer (i + 2)).subgroupOf (S.layer (i + 1)))
            (⟨S.C.x r.root
              (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j),
              htermMem r hr⟩ : S.layer (i + 1))) = 1 := by
      have hrvalid := (hvalid r).mp hr
      have hrheight := relativeRootHeight_of_validChevalleyCommutatorTerm
        S.D S.rootPairing S.rootEquiv S.rootBase
          (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion r hrvalid
      have hGamma : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv gamma.1) = (i : ℤ) := by
        simpa only [S.rootBase_support] using gamma.2
      have hBeta : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv beta.1) = (1 : ℤ) := by
        simpa only [S.rootBase_support, Nat.cast_one] using beta.2
      have hheight : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv r.root) =
          r.i * (i : ℤ) + r.j := by
        rw [hrheight, hGamma, hBeta]
        ring
      by_cases hexact : RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) (S.rootEquiv r.root) = (i + 1 : ℤ)
      · have hri : r.i = 1 := by
          have hriPos : 0 < r.i := hrvalid.1
          have hrjPos : 0 < r.j := hrvalid.2.1
          rw [hheight] at hexact
          nlinarith
        have hrj : r.j = 1 := by
          have hriPos : 0 < r.i := hrvalid.1
          have hrjPos : 0 < r.j := hrvalid.2.1
          rw [hheight] at hexact
          nlinarith
        let rIndex : S.layerRootIndex (i + 1) := ⟨r.root, by
          simpa only [S.rootBase_support, Nat.cast_add, Nat.cast_one] using hexact⟩
        have hrne : rIndex ≠ delta := by
          intro heq
          have hrootEq : S.rootPairing.root (S.rootEquiv gamma.1) =
              S.rootPairing.root (S.rootEquiv alpha.1) := by
            have htermRoot := hrvalid.2.2
            have hdelta : r.root = delta.1 := by
              simpa [rIndex] using congrArg Subtype.val heq
            rw [hdelta, hroot, hri, hrj] at htermRoot
            simpa [add_left_inj, add_right_inj] using htermRoot.symm
          apply hgamma
          apply Subtype.ext
          apply S.rootEquiv.injective
          exact S.rootPairing.root.injective hrootEq
        have htermEq :
            (⟨S.C.x r.root
              (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j),
              htermMem r hr⟩ : S.layer (i + 1)) =
              S.layerRootElement (i + 1) rIndex
                (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j) := by
          apply Subtype.ext
          exact (S.layerRootElement_value (i + 1) rIndex
            (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j)).symm
        rw [htermEq]
        rw [layerQuotientCoordinateAt_root]
        simp [hrne]
      · apply layerQuotientCoordinateAt_deep
        have hri : (1 : ℤ) ≤ r.i := by
          exact_mod_cast (Nat.succ_le_of_lt hrvalid.1)
        have hrj : (1 : ℤ) ≤ r.j := by
          exact_mod_cast (Nat.succ_le_of_lt hrvalid.2.1)
        have hdeep : (i + 2 : ℤ) ≤ RelativeRootHeight S.coeff
            S.rootBase.support (S.rootEquiv '' S.J) (S.rootEquiv r.root) := by
          rw [hheight]
          have hbase : (i + 1 : ℤ) ≤ r.i * (i : ℤ) + r.j := by
            nlinarith
          omega
        rw [ParabolicRelativeRootSetup.layer, ← S.rootBase_support,
          RelativeRootSeries, RootSubgroupGenerated]
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨r.root, hdeep, by
          rw [← (S.chevalleySystem.1 r.root).2]
          exact Set.mem_range_self _⟩
    have hzeroGamma : S.C.x gamma.1 0 = 1 := by
      simpa using (S.chevalleySystem.2.2.2.1 gamma.1 0 0)
    have hzeroBeta : S.C.x beta.1 0 = 1 := by
      simpa using (S.chevalleySystem.2.2.2.1 beta.1 0 0)
    have hxinv : S.C.x gamma.1 (-t) = (S.C.x gamma.1 t)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [S.chevalleySystem.2.2.2.1 gamma.1 (-t) t]
      simpa using hzeroGamma
    have hyinv : S.C.x beta.1 (-1) = (S.C.x beta.1 1)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [S.chevalleySystem.2.2.2.1 beta.1 (-1) 1]
      simpa using hzeroBeta
    have hformula' := hformula (-t) (-1)
    have hcommWord' : (commNext : Variety.Point K) =
        (order.map fun r => S.C.x r.root
          (coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j)).prod := by
      change ⁅(gammaLayer : Variety.Point K), (betaLayer : Variety.Point K)⁆ = _
      rw [show (gammaLayer : Variety.Point K) = S.C.x gamma.1 t by
          exact S.layerRootElement_value i gamma t,
        show (betaLayer : Variety.Point K) = S.C.x beta.1 1 by
          exact S.layerRootElement_value 1 beta 1]
      simpa [hxinv, hyinv, commutatorElement_def, mul_assoc] using hformula'
    have hcommWord : (commNext : Variety.Point K) =
        ChevalleyCommutatorTermWordProduct S.C
          (order.map fun r =>
            (r, coefficient r * (-t) ^ r.i * (-1 : k) ^ r.j)) := by
      simpa [ChevalleyCommutatorTermWordProduct,
        List.map_map, Function.comp_def] using hcommWord'
    let termNext (r : { r // r ∈ order }) : S.layer (i + 1) :=
      ⟨S.C.x r.1.root
        (coefficient r.1 * (-t) ^ r.1.i * (-1 : k) ^ r.1.j),
        htermMem r.1 r.2⟩
    have hcommNextWord : commNext =
        (order.attach.map termNext).prod := by
      apply Subtype.ext
      simpa [termNext, ChevalleyCommutatorTermWordProduct,
        List.map_map, Function.comp_def, mul_assoc] using hcommWord
    let targetCharacter : S.layer (i + 1) →* Multiplicative k :=
      (layerQuotientCoordinateAt S (i + 1) (by omega) delta).comp
        (QuotientGroup.mk' ((S.layer (i + 2)).subgroupOf (S.layer (i + 1))))
    change targetCharacter commNext = 1
    rw [hcommNextWord, targetCharacter.map_list_prod]
    apply List.prod_eq_one
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨z, hz, rfl⟩
    rw [List.mem_map] at hz
    rcases hz with ⟨r, _hr, rfl⟩
    exact hterm r.1 r.2

private theorem fixedLayerCoordinateCommutatorHom_at
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k))
    (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (beta : S.layerRootIndex 1)
    (delta : S.layerRootIndex (i + 1))
    (hroot : S.rootPairing.root (S.rootEquiv delta.1) =
      S.rootPairing.root (S.rootEquiv alpha.1) +
        S.rootPairing.root (S.rootEquiv beta.1)) :
    ∃ c : k, c ≠ 0 ∧ ∀ f : Multiplicative (S.layerRootIndex i → k),
      multiplicativeEval delta
        (fixedLayerCoordinateCommutatorHom S i hi
          (S.layerRootElement 1 beta 1) f) =
        Multiplicative.ofAdd (c * (Multiplicative.toAdd f) alpha) := by
  classical
  letI := Fintype.ofFinite (S.layerRootIndex i)
  obtain ⟨c, hc, hselected⟩ := fixedLayerCoordinateCommutatorHom_root
    S classification hType hNonsingular i hi alpha beta delta hroot
  refine ⟨c, hc, ?_⟩
  intro f
  let H : Multiplicative (S.layerRootIndex i → k) →* Multiplicative k :=
    (multiplicativeEval delta).comp
      (fixedLayerCoordinateCommutatorHom S i hi
        (S.layerRootElement 1 beta 1))
  have hf : f = ∏ gamma : S.layerRootIndex i,
      Multiplicative.ofAdd
        (Pi.single gamma ((Multiplicative.toAdd f) gamma)) := by
    ext z
    simp
  change H f = _
  conv_lhs => rw [hf]
  rw [map_prod]
  rw [Finset.prod_eq_single alpha]
  · change multiplicativeEval delta
        (fixedLayerCoordinateCommutatorHom S i hi
          (S.layerRootElement 1 beta 1)
          (Multiplicative.ofAdd
            (Pi.single alpha ((Multiplicative.toAdd f) alpha)))) = _
    rw [hselected ((Multiplicative.toAdd f) alpha)]
    simp [multiplicativeEval]
  · intro gamma _hgamma hne
    exact fixedLayerCoordinateCommutatorHom_root_at_of_ne
      S i hi alpha gamma beta delta hroot hne _
  · simp

private theorem diagonal_base_of_diagonal_base
    {I X Y : Type*} [Finite I]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (P : RootPairing I ℚ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdiag : ∀ s t : b.support, s ≠ t → b.cartanMatrix s t = 0)
    (b' : P.Base) :
    ∀ s t : b'.support, s ≠ t → b'.cartanMatrix s t = 0 := by
  let := P.indexNeg
  intro s t hst
  obtain ⟨js, hs | hs⟩ := diagonal_base_root_eq_or_neg P b hdiag s
  · obtain ⟨jt, ht | ht⟩ := diagonal_base_root_eq_or_neg P b hdiag t
    · have hjne : js ≠ jt := by
        intro heq
        apply hst
        apply Subtype.ext
        apply P.root.injective
        rw [hs, ht, heq]
      change P.pairingIn ℤ s t = 0
      have hz := hdiag js jt hjne
      change P.pairingIn ℤ js jt = 0 at hz
      have hsidx : (s : I) = js := P.root.injective hs
      have htidx : (t : I) = jt := P.root.injective ht
      simpa [hsidx, htidx] using hz
    · have hjne : js ≠ jt := by
        intro heq
        have hrootneg : P.root s = -P.root t := by
          rw [hs, ht, heq]
          simp
        have hidx : (s : I) = -t := by
          apply P.root.injective
          simpa using hrootneg
        have hsPos := b'.isPos_of_mem_support s.2
        have htPos := b'.isPos_of_mem_support t.2
        have hnegPos : b'.IsPos (-t) := by simpa [hidx] using hsPos
        exact ((RootPairing.Base.IsPos.neg_iff_not b' t).mp hnegPos) htPos
      change P.pairingIn ℤ s t = 0
      have hz := hdiag js jt hjne
      change P.pairingIn ℤ js jt = 0 at hz
      have hsidx : (s : I) = js := P.root.injective hs
      have htidx : (t : I) = -jt := by
        apply P.root.injective
        simpa using ht
      simp [hsidx, htidx, hz]
  · obtain ⟨jt, ht | ht⟩ := diagonal_base_root_eq_or_neg P b hdiag t
    · have hjne : js ≠ jt := by
        intro heq
        have hrootneg : P.root t = -P.root s := by
          rw [hs, ht, heq]
          simp
        have hidx : (t : I) = -s := by
          apply P.root.injective
          simpa using hrootneg
        have hsPos := b'.isPos_of_mem_support s.2
        have htPos := b'.isPos_of_mem_support t.2
        have hnegPos : b'.IsPos (-s) := by simpa [hidx] using htPos
        exact ((RootPairing.Base.IsPos.neg_iff_not b' s).mp hnegPos) hsPos
      change P.pairingIn ℤ s t = 0
      have hz := hdiag js jt hjne
      change P.pairingIn ℤ js jt = 0 at hz
      have hsidx : (s : I) = -js := by
        apply P.root.injective
        simpa using hs
      have htidx : (t : I) = jt := P.root.injective ht
      simp [hsidx, htidx, hz]
    · have hjne : js ≠ jt := by
        intro heq
        apply hst
        apply Subtype.ext
        apply P.root.injective
        rw [hs, ht, heq]
      change P.pairingIn ℤ s t = 0
      have hz := hdiag js jt hjne
      change P.pairingIn ℤ js jt = 0 at hz
      have hsidx : (s : I) = -js := by
        apply P.root.injective
        simpa using hs
      have htidx : (t : I) = -jt := by
        apply P.root.injective
        simpa using ht
      simp [hsidx, htidx, hz]

omit [IsAlgClosed k] in
private theorem irreducible_of_relative_height_below_max
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (alpha : S.ι)
    (hpositive : 1 ≤ RelativeRootHeight S.coeff S.rootBase.support
      (S.rootEquiv '' S.J) alpha)
    (hbelow : RelativeRootHeight S.coeff S.rootBase.support
      (S.rootEquiv '' S.J) alpha < S.maxRelativeHeight) :
    S.rootPairing.IsIrreducible := by
  classical
  letI := Fintype.ofFinite S.ι
  letI := S.rootPairing.indexNeg
  letI : Nonempty S.ι := ⟨alpha⟩
  rcases irreducible_or_diagonal_of_hasDynkinType
      S.rootPairing classification hType with hirred | ⟨base, hdiag⟩
  · exact hirred
  · exfalso
    have hrootDiag := diagonal_base_of_diagonal_base
      S.rootPairing base hdiag S.rootBase
    rcases S.relativeHeight_eq with ⟨_, hmax⟩ | ⟨theta, _, htheta⟩
    · omega
    · obtain ⟨j, hj | hj⟩ := diagonal_base_root_eq_or_neg
        S.rootPairing S.rootBase hrootDiag (S.rootEquiv theta)
      · have hindex : S.rootEquiv theta = j :=
          S.rootPairing.root.injective hj
        rw [hindex] at htheta
        by_cases hjJ : (j : S.ι) ∈ S.rootEquiv '' S.J
        · rw [(relativeRootHeight_eq_zero_iff_mem S.rootPairing S.rootBase
              (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion j.2).2 hjJ]
            at htheta
          omega
        · rw [(relativeRootHeight_eq_one_iff_not_mem S.rootPairing S.rootBase
              (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion j.2).2 hjJ]
            at htheta
          omega
      · have hthetaPositive : S.rootBase.IsPos (S.rootEquiv theta) :=
          base_isPos_of_relativeRootHeight_pos S.rootPairing S.rootBase
            (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion (by omega)
        have hindex : S.rootEquiv theta = -j := by
          apply S.rootPairing.root.injective
          simpa using hj
        have hnegPositive : S.rootBase.IsPos (-j) := by
          simpa [hindex] using hthetaPositive
        exact ((RootPairing.Base.IsPos.neg_iff_not S.rootBase j).mp hnegPositive)
          (S.rootBase.isPos_of_mem_support j.2)

/-- An element that first appears in a relative-root layer is detected one
step farther down by commutation with a height-one root element. -/
public theorem ParabolicRelativeRootSetup.upper_commutator_detection
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k)) :
    ∀ n, n < S.maxRelativeHeight →
      ∀ x : S.U.toSubgroup,
        x ∉ (S.layer (S.maxRelativeHeight - n)).subgroupOf S.U.toSubgroup →
        ∃ y : S.U.toSubgroup,
          ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉
            S.layer (S.maxRelativeHeight + 1 - n) := by
  classical
  letI := Fintype.ofFinite S.ι
  intro n hn x hx
  let h := S.maxRelativeHeight - n
  have hhPositive : 0 < h := by
    dsimp [h]
    omega
  have hxNotH : (x : Variety.Point K) ∉ S.layer h := by
    intro hxH
    apply hx
    exact (Subgroup.mem_subgroupOf.mpr hxH)
  have hxFirst : (x : Variety.Point K) ∈ S.layer 1 := by
    rw [← S.unipotent_eq_first_layer]
    exact x.2
  let Bad : ℕ → Prop := fun j =>
    (x : Variety.Point K) ∉ S.layer (j + 1)
  have hBad : ∃ j, Bad j := by
    refine ⟨h - 1, ?_⟩
    simpa only [Bad, Nat.sub_add_cancel hhPositive] using hxNotH
  let i := Nat.find hBad
  have hiNotNext : (x : Variety.Point K) ∉ S.layer (i + 1) := by
    exact Nat.find_spec hBad
  have hiPositive : 0 < i := by
    apply (Nat.find_pos hBad).2
    simp only [Bad, Nat.zero_add, not_not]
    exact hxFirst
  have hxLayer : (x : Variety.Point K) ∈ S.layer i := by
    have hpred : i - 1 < i := by omega
    have hnotBad := Nat.find_min hBad hpred
    simp only [Bad, not_not] at hnotBad
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hnotBad
  have hiLtH : i < h := by
    have hminimal : i ≤ h - 1 := Nat.find_min' hBad (by
      simpa only [Bad, Nat.sub_add_cancel hhPositive] using hxNotH)
    omega
  have hiLtMax : i < S.maxRelativeHeight := by
    dsimp [h] at hiLtH
    omega
  letI := parabolicRelativeRootLayer_next_normal S i hiPositive
  let xi : S.layer i := ⟨x, hxLayer⟩
  let q : S.layer i ⧸
      (S.layer (i + 1)).subgroupOf (S.layer i) :=
    QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i)) xi
  have hqNe : q ≠ 1 := by
    intro hq
    apply hiNotNext
    exact (QuotientGroup.eq_one_iff xi).mp hq
  let f : Multiplicative (S.layerRootIndex i → k) :=
    parabolicRelativeRootLayer_quotientCoordinateEquiv S i hiPositive q
  have hfNe : f ≠ 1 := by
    intro hf
    apply hqNe
    apply (parabolicRelativeRootLayer_quotientCoordinateEquiv
      S i hiPositive).injective
    simpa only [f, map_one] using hf
  obtain ⟨alpha, hAlphaCoordinate⟩ :
      ∃ alpha : S.layerRootIndex i,
        (Multiplicative.toAdd f) alpha ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hfNe
    ext alpha
    change (Multiplicative.toAdd f) alpha = 0
    exact hnone alpha
  have hAlphaHeight : RelativeRootHeight S.coeff S.rootBase.support
      (S.rootEquiv '' S.J) (S.rootEquiv alpha.1) = i := by
    simpa only [S.rootBase_support] using alpha.2
  letI : S.rootPairing.IsIrreducible :=
    irreducible_of_relative_height_below_max S classification hType
      (S.rootEquiv alpha.1) (by rw [hAlphaHeight]; exact_mod_cast hiPositive)
      (by rw [hAlphaHeight]; exact_mod_cast hiLtMax)
  have hJ : S.rootEquiv '' S.J ⊆ S.rootBase.support := by
    rintro _ ⟨gamma, hgamma, rfl⟩
    exact (S.rootSystemRealization.2.2.2.1 gamma).1
      (S.standardParabolic.2.1 hgamma)
  have hMax :
      (∀ gamma, RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) gamma ≤ S.maxRelativeHeight) ∧
        ∃ gamma, RelativeRootHeight S.coeff S.rootBase.support
          (S.rootEquiv '' S.J) gamma = S.maxRelativeHeight := by
    constructor
    · intro gamma
      simpa using S.relativeHeight_le (S.rootEquiv.symm gamma)
    · rcases S.relativeHeight_eq with ⟨_, hmaxZero⟩ | ⟨theta, _, htheta⟩
      · omega
      · exact ⟨S.rootEquiv theta, htheta⟩
  obtain ⟨betaIndex, deltaIndex, hroot, hBetaHeight⟩ :=
    relativeRootHeight_extension_below_max S.rootPairing S.rootBase
      (S.rootEquiv '' S.J) hJ S.coeff S.rootSimpleRootExpansion
      S.maxRelativeHeight hMax (S.rootEquiv alpha.1)
      (by rw [hAlphaHeight]; exact_mod_cast hiPositive)
      (by rw [hAlphaHeight]; exact_mod_cast hiLtMax)
  let beta : S.layerRootIndex 1 :=
    ⟨S.rootEquiv.symm betaIndex, by
      simpa only [← S.rootBase_support, Equiv.apply_symm_apply,
        Nat.cast_one] using hBetaHeight⟩
  have hDeltaHeight : RelativeRootHeight S.coeff S.rootBase.support
      (S.rootEquiv '' S.J) deltaIndex = i + 1 := by
    rw [relativeRootHeight_eq_add_of_root_eq_add S.rootPairing S.rootBase
      (S.rootEquiv '' S.J) S.coeff S.rootSimpleRootExpansion hroot,
      hAlphaHeight, hBetaHeight]
  let delta : S.layerRootIndex (i + 1) :=
    ⟨S.rootEquiv.symm deltaIndex, by
      simpa only [← S.rootBase_support, Equiv.apply_symm_apply,
        Nat.cast_add, Nat.cast_one] using hDeltaHeight⟩
  have hrootActual : S.rootPairing.root (S.rootEquiv delta.1) =
      S.rootPairing.root (S.rootEquiv alpha.1) +
        S.rootPairing.root (S.rootEquiv beta.1) := by
    simpa only [delta, beta, Equiv.apply_symm_apply] using hroot
  let yLayer : S.layer 1 := S.layerRootElement 1 beta 1
  let y : S.U.toSubgroup := ⟨yLayer, by
    rw [S.unipotent_eq_first_layer]
    exact yLayer.2⟩
  obtain ⟨c, hc, hcoordinate⟩ :=
    fixedLayerCoordinateCommutatorHom_at S classification hType
      hNonsingular i hiPositive alpha beta delta hrootActual
  have hSelectedNe : multiplicativeEval delta
      (fixedLayerCoordinateCommutatorHom S i hiPositive yLayer f) ≠ 1 := by
    rw [hcoordinate f]
    change c * (Multiplicative.toAdd f) alpha ≠ 0
    exact mul_ne_zero hc hAlphaCoordinate
  have hCommLe : ⁅S.layer i, S.layer 1⁆ ≤ S.layer (i + 1) := by
    simpa only [ParabolicRelativeRootSetup.layer, ← S.rootBase_support] using
      relativeRootSeries_commutator_series_le S.D S.C S.rootPairing
        S.rootEquiv S.rootBase S.coeff S.rootSimpleRootExpansion
        S.chevalleySystem S.J i hiPositive
  let commNext : S.layer (i + 1) :=
    ⟨⁅(x : Variety.Point K), (y : Variety.Point K)⁆,
      hCommLe (Subgroup.commutator_mem_commutator hxLayer yLayer.2)⟩
  letI := parabolicRelativeRootLayer_next_normal S (i + 1) (by omega)
  have hFixed : fixedLayerCoordinateCommutatorHom S i hiPositive yLayer f =
      parabolicRelativeRootLayer_quotientCoordinateEquiv S (i + 1) (by omega)
        (QuotientGroup.mk'
          ((S.layer (i + 2)).subgroupOf (S.layer (i + 1))) commNext) := by
    change parabolicRelativeRootLayer_quotientCoordinateEquiv S (i + 1) (by omega)
        (fixedLayerQuotientCommutatorHom S i hiPositive yLayer
          (parabolicRelativeRootLayer_coordinateHom S i hiPositive f)) = _
    rw [parabolicRelativeRootLayer_coordinateHom_quotientCoordinateEquiv
      S i hiPositive q]
    rfl
  have hCommQuotientNe :
      (QuotientGroup.mk'
        ((S.layer (i + 2)).subgroupOf (S.layer (i + 1))) commNext) ≠ 1 := by
    intro hcommOne
    apply hSelectedNe
    rw [hFixed, hcommOne]
    simp
  have hCommNotDeep :
      ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉ S.layer (i + 2) := by
    intro hdeep
    apply hCommQuotientNe
    exact (QuotientGroup.eq_one_iff commNext).2 hdeep
  refine ⟨y, ?_⟩
  intro htarget
  apply hCommNotDeep
  have hindex : i + 2 ≤ S.maxRelativeHeight + 1 - n := by
    dsimp [h] at hiLtH
    omega
  exact (relativeRootSeries_antitone S.D S.rootEquiv S.base.support
    S.coeff S.J hindex) htarget

end Theory.AlgebraicGroup
