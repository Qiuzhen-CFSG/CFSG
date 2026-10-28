module

public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# Faithfulness of the full central triality Levi

The two highest long-root groups in the central radical detect the two
natural root-string columns of the actual central SL₂ representation.
A centralizing full Levi element must therefore have a diagonal SL₂ factor,
so it belongs to the original split torus. The highest-root weight makes
its central coroot coordinate one. The first folded short root recovers
the squares of all three arm coordinates; square injectivity in
characteristic two makes those coordinates one as well.

The calculation uses actual Geck root curves, the proved pinned rank-one
identification, and the full split Levi factorization. It is transferred
through the elementary subgroup and its own central quotient using the
proved injectivity of that quotient in characteristic two. All parameters,
including q = 2, are retained; no perfectness assertion is used.

Source: GLS3 Theorem 2.6.5(e–g) and the root formulas of §2.4
(`refs/KGroup/GLS3/chapter2.tex`); the central local group in
Aschbacher–Smith F.1.12(I)(4), pp.263–264 (`refs/quasithin.pdf`).
-/


open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices

namespace Triality.Standard.Parabolics
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private lemma rankOne_entry (P : Parameters) (hp : P.prime = 2) (A : SL(2, ExtensionField P))
    (r s : BlockIndex) :
    matrixHom P ((pinnedRankOneMaps P hp).hom 1 A)
      (latticeEnumeration.symm (latticeEquiv 1 r))
      (latticeEnumeration.symm (latticeEquiv 1 s)) = blockMatrix 1 A r s := by
  let := rankOneExtensionCharTwo P hp
  change (ambientHom 1 A).val
    (latticeEnumeration (latticeEnumeration.symm (latticeEquiv 1 r)))
    (latticeEnumeration (latticeEnumeration.symm (latticeEquiv 1 s))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ambientHom_entry 1 A r s

private lemma flat_block (r : BlockIndex) :
  latticeEnumeration.symm (latticeEquiv 1 r) =
    match r with
    | .inl (.inl j) => .inl j
    | .inl (.inr j) => .inr (rootOrder 1 (rootBlockEnumeration (.inl j)))
    | .inr j => .inr (rootOrder 1 (rootBlockEnumeration (.inr j))) := by
  rcases r with (j | j) | j <;> simp [latticeEnumeration, latticeEquiv]

private lemma rankOne_column (P : Parameters) (hp : P.prime = 2) (A : SL(2, ExtensionField P))
    (r : Index) : matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) r (.inl 1) =
      (1 : Matrix Index Index (ExtensionField P)) r (.inl 1) := by
  obtain ⟨r, rfl⟩ := ((latticeEquiv 1).trans latticeEnumeration.symm).surjective r
  have he := rankOne_entry P hp A r (.inl (.inl 1))
  rcases r with (r | r) | (r | r)
  all_goals simpa [Equiv.trans_apply, flat_block, blockMatrix, specialBlock,
    adjacent, Matrix.one_apply] using he

private lemma flat_natural (r : Fin 2) :
    latticeEnumeration.symm (latticeEquiv 1 (.inr (.inl (r,0)))) =
      .inr (![0,4] r) := by
  rw [flat_block]
  fin_cases r <;> rfl

private lemma rankOne_natural_entry (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (r s : Fin 2) :
    matrixHom P ((pinnedRankOneMaps P hp).hom 1 A)
      (.inr (![0,4] r)) (.inr (![0,4] s)) = A r s := by
  have hh := rankOne_entry P hp A (.inr (.inl (r,0))) (.inr (.inl (s,0)))
  simpa only [flat_natural, blockMatrix, Matrix.fromBlocks_apply₂₂,
    Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply_eq] using hh

private lemma torus_diagonal (P : Parameters) (hp : P.prime = 2)
    (t : SplitGroup P) (ht : t ∈ splitTorus P) :
    ∃ d : Index → ExtensionField P,
      matrixHom P t = Matrix.diagonal d ∧ d (.inl 1) = 1 ∧ ∀ r, d r ≠ 0 := by
  obtain ⟨a, rfl⟩ := (Set.ext_iff.mp (range_product P hp) t).mpr ht
  refine ⟨fun r => (a 0).val ^ corootWeight 0 (latticeEnumeration r) *
    (a 2).val ^ corootWeight 2 (latticeEnumeration r) *
    (a 3).val ^ corootWeight 3 (latticeEnumeration r) *
    (a 1).val ^ corootWeight 1 (latticeEnumeration r), ?_, ?_, ?_⟩
  · ext r s
    change (product P a).val.val (latticeEnumeration r) (latticeEnumeration s) = _
    rw [product_val P hp]
    simp [Matrix.diagonal_apply]
  · simp [latticeEnumeration, corootWeight]
  · intro r
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (a 0).ne_zero)
      (zpow_ne_zero _ (a 2).ne_zero)) (zpow_ne_zero _ (a 3).ne_zero))
      (zpow_ne_zero _ (a 1).ne_zero)

/-- The two highest roots have unit coefficient on the central Cartan column. -/
private lemma long_column (j : Fin 2) (r : Index) :
    linearCoefficient (![4, 0] j) r (.inl 1) =
      (if r = .inr (![4, 0] j) then 1 else 0) ∧
    quadraticCoefficient (![4, 0] j) r (.inl 1) = 0 := by
  revert j r
  decide +kernel

private lemma commuting_column {F : Type*} [Field F] [CharP F 2]
    (A : Matrix Index Index F) (k : Fin 24)
    (hc : ∀ r, A r (.inl 1) = (1 : Matrix Index Index F) r (.inl 1))
    (he : ∀ r, matrixCurve k (1 : F) r (.inl 1) =
      (1 : Matrix Index Index F) r (.inl 1) + if r = .inr k then 1 else 0)
    (h : Commute A (matrixCurve k (1 : F))) (r : Index) :
    A r (.inr k) = (1 : Matrix Index Index F) r (.inr k) := by
  have hh := congrFun₂ h.eq r (.inl 1)
  simp only [Matrix.mul_apply, he, hc, mul_add, Finset.sum_add_distrib] at hh
  simp only [← Matrix.mul_apply, mul_one] at hh
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  rw [hc, he] at hh
  exact add_left_cancel hh

private lemma long_commuting_column (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hc : ∀ r, matrixHom P g r (.inl 1) =
      (1 : Matrix Index Index (ExtensionField P)) r (.inl 1))
    (j : Fin 2) (h : Commute g (curve P (![10,11] j) 1)) (r : Index) :
    matrixHom P g r (.inr (![4,0] j)) =
      (1 : Matrix Index Index (ExtensionField P)) r (.inr (![4,0] j)) := by
  let := rankOneExtensionCharTwo P hp
  have hh := h.map (matrixHom P)
  rw [matrixHom_curve P hp] at hh
  have hj : positiveIndex (![10,11] j) = ![4,0] j := by fin_cases j <;> rfl
  rw [hj] at hh
  apply commuting_column _ _ hc ?_ hh r
  intro s
  obtain ⟨hl, hq⟩ := long_column j s
  simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq]

/-- Fixing both long-root vectors kills both off-diagonal entries of the actual
central rank-one matrix. The torus contributes only nonzero column scalars. -/
private lemma rankOne_off_diagonal (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (t : SplitGroup P) (ht : t ∈ splitTorus P)
    (h : ∀ j : Fin 2, Commute ((pinnedRankOneMaps P hp).hom 1 A * t)
      (curve P (![10,11] j) 1)) : A 0 1 = 0 ∧ A 1 0 = 0 := by
  obtain ⟨d, hd, hd1, hdn⟩ := torus_diagonal P hp t ht
  have hc (r : Index) :
      matrixHom P ((pinnedRankOneMaps P hp).hom 1 A * t) r (.inl 1) =
        (1 : Matrix Index Index (ExtensionField P)) r (.inl 1) := by
    rw [map_mul, hd, Matrix.mul_diagonal, hd1, mul_one, rankOne_column]
  have h01 := long_commuting_column P hp _ hc 0 (h 0) (.inr 0)
  have h10 := long_commuting_column P hp _ hc 1 (h 1) (.inr 4)
  have he01 := rankOne_natural_entry P hp A 0 1
  have he10 := rankOne_natural_entry P hp A 1 0
  change matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) (.inr 0) (.inr 4) = _ at he01
  change matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) (.inr 4) (.inr 0) = _ at he10
  simp only [map_mul, Matrix.mul_diagonal, hd] at h01 h10
  change matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) (.inr 0) (.inr 4) * d (.inr 4) = 0 at h01
  change matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) (.inr 4) (.inr 0) * d (.inr 0) = 0 at h10
  rw [he01] at h01
  rw [he10] at h10
  exact ⟨(mul_eq_zero.mp h01).resolve_right (hdn _), (mul_eq_zero.mp h10).resolve_right (hdn _)⟩

private abbrev up {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev dn {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t
private def torusSL {F : Type*} [Field F] (t : Fˣ) : SL(2, F) :=
  (up t.val * dn (-t.val⁻¹) * up t.val) * (up (-1) * dn 1 * up (-1))

private lemma torusSL_val {F : Type*} [Field F] (t : Fˣ) :
    (torusSL t).val = !![t.val, 0; 0, t.val⁻¹] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [torusSL, up, dn, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, t.ne_zero]

private lemma diagonal_rankOne_mem_torus (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    (pinnedRankOneMaps P hp).hom 1 A ∈ splitTorus P := by
  have hdet : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] using A.det_coe
  have hne : A 0 0 ≠ 0 := by intro h; simp [h] at hdet
  let u : (ExtensionField P)ˣ := Units.mk0 (A 0 0) hne
  have he : A = torusSL u := by
    apply Subtype.ext
    rw [torusSL_val]
    have hinv : A 1 1 = (A 0 0)⁻¹ := by
      apply (mul_left_cancel₀ hne)
      rw [hdet, mul_inv_cancel₀ hne]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [u, h01, h10, hinv]
  rw [he]
  have hh : (pinnedRankOneMaps P hp).hom 1 (torusSL u) = torusWord P 1 u := by
    simp only [torusSL, up, dn, map_mul, PinnedRankOneMaps.positive,
      PinnedRankOneMaps.negative]
    simp only [torusWord, weylWord, inv_neg, inv_one, neg_neg]
  rw [hh]
  exact Subgroup.subset_closure ⟨1, u, rfl⟩

/-- The split full Levi has its genuine subsystem-times-torus factorization. -/
private lemma central_fullLevi_mem_torus (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ splitFullLevi P .central)
    (h : ∀ j : Fin 2, Commute g (curve P (![10,11] j) 1)) :
    g ∈ splitTorus P := by
  have hg' := (Set.ext_iff.mp (splitFullLevi_eq_mul_centralTorus P hp .central) g).mp hg
  obtain ⟨l, hl, t, ht, rfl⟩ := hg'
  rw [← (pinnedRankOneMaps P hp).range_central] at hl
  obtain ⟨A, rfl⟩ := hl
  obtain ⟨h01, h10⟩ := rankOne_off_diagonal P hp A t ht.1 h
  exact (splitTorus P).mul_mem (diagonal_rankOne_mem_torus P hp A h01 h10) ht.1

private lemma conj_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
private lemma conj_root_product {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

private def testRoot : Fin 4 → Fin 12 := ![0,1,2,11]
private def testWeight : Fin 4 → Fin 4 → ℤ :=
  ![![2,-1,0,0], ![0,-1,2,0], ![0,-1,0,2], ![0,1,0,0]]

private lemma test_pairing (j i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (testRoot j))
      (typeDSimpleRootIndex 2 i) = testWeight j i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex (testRoot j)) k) = testWeight j i := by
    revert j i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (testWeight j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private lemma product_test_conjugate (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (j : Fin 4) (u : ExtensionField P) :
    product P a * curve P (testRoot j) u * (product P a)⁻¹ =
      curve P (testRoot j) ((a 0).val ^ testWeight j 0 *
        ((a 2).val ^ testWeight j 2 *
          ((a 3).val ^ testWeight j 3 * ((a 1).val ^ testWeight j 1 * u)))) := by
  simp only [product, conj_product, torusWord_curve_conjugate P hp, test_pairing]

private lemma triple_injective (P : Parameters) (a b : Fin 3 → ExtensionField P)
    (he : curve P 0 (a 0) * curve P 1 (a 1) * curve P 2 (a 2) =
      curve P 0 (b 0) * curve P 1 (b 1) * curve P 2 (b 2)) : a = b := by
  let va : PositiveCoordinates.Coordinates P := ![a 0,a 1,a 2,0,0,0,0,0,0,0,0,0]
  let vb : PositiveCoordinates.Coordinates P := ![b 0,b 1,b 2,0,0,0,0,0,0,0,0,0]
  have hh : orderedProduct P va = orderedProduct P vb := by
    simpa [va, vb, orderedProduct, List.ofFn_succ, mul_assoc] using he
  have hv := orderedProduct_injective P hh
  funext j
  fin_cases j
  · exact congrFun hv 0
  · exact congrFun hv 1
  · exact congrFun hv 2

private lemma last_curve_injective (P : Parameters) : Function.Injective (curve P 11) := by
  intro u v h
  have he : orderedProduct P (Function.update 0 11 u) =
      orderedProduct P (Function.update 0 11 v) := by
    simpa [orderedProduct, List.ofFn_succ] using h
  have hh := congrFun (orderedProduct_injective P he) 11
  simpa using hh

/-- The highest-root weight is the central coroot coordinate. The three first
short-root weights then recover the squares of the three arm coordinates. -/
private lemma torus_eq_one_of_test_roots (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ splitTorus P)
    (hs : Commute g (shortSplit P 0 1)) (hl : Commute g (curve P 11 1)) : g = 1 := by
  let := rankOneExtensionCharTwo P hp
  obtain ⟨a, rfl⟩ := (Set.ext_iff.mp (range_product P hp) g).mpr hg
  have hlast := product_test_conjugate P hp a 3 1
  have hc : (a 1).val = 1 := by
    apply last_curve_injective P
    simpa [testRoot, testWeight] using hlast.symm.trans hl.mul_inv_cancel
  have hfirst := hs.mul_inv_cancel
  simp only [shortSplit, map_one, conj_root_product] at hfirst
  have hc0 := product_test_conjugate P hp a 0 1
  have hc1 := product_test_conjugate P hp a 1 1
  have hc2 := product_test_conjugate P hp a 2 1
  simp [testRoot, testWeight, hc] at hc0 hc1 hc2
  change (product P a * curve P 0 1 * (product P a)⁻¹) *
      (product P a * curve P 1 1 * (product P a)⁻¹) *
      (product P a * curve P 2 1 * (product P a)⁻¹) =
        curve P 0 1 * curve P 1 1 * curve P 2 1 at hfirst
  have hsquares := (congrArg₂ (· * ·) (congrArg₂ (· * ·) hc0 hc1) hc2).symm.trans hfirst
  have hv := triple_injective P
    (![(a 0).val ^ 2, (a 2).val ^ 2, (a 3).val ^ 2]) (![1,1,1]) hsquares
  have ha : a = 1 := by
    funext i
    apply Units.ext
    fin_cases i
    · exact CharTwo.sq_injective (by simpa using congrFun hv 0)
    · exact hc
    · exact CharTwo.sq_injective (by simpa using congrFun hv 1)
    · exact CharTwo.sq_injective (by simpa using congrFun hv 2)
  rw [ha, product_one P hp]

private lemma lift_commute (P : Parameters) (hp : P.prime = 2) (x y : ElementaryGroup P)
    (h : Commute (toCarrier P x) (toCarrier P y)) :
    Commute (elementaryInclusion P x) (elementaryInclusion P y) := by
  have he : Commute x y := Commute.of_map (ElementaryCentralKernel.toCarrier_injective P hp) h
  exact he.map (elementaryInclusion P)

private lemma elementary_centralizer_eq_one (P : Parameters) (hp : P.prime = 2)
    (x : ElementaryGroup P) (hx : elementaryInclusion P x ∈ splitFullLevi P .central)
    (hk : toCarrier P x ∈ Subgroup.centralizer (radical P .central : Set (Carrier P))) :
    x = 1 := by
  have hcomm (y : ElementaryGroup P)
      (hy : toCarrier P y ∈ descendSubgroup P (rootSubgroup P .central)) :
      Commute (elementaryInclusion P x) (elementaryInclusion P y) := by
    have hyr : toCarrier P y ∈ radical P .central :=
      (radical_eq_descendedRootSubgroup P hp .central).ge hy
    exact lift_commute P hp x y
      (show Commute (toCarrier P y) (toCarrier P x) from
        Subgroup.mem_centralizer_iff.mp hk _ hyr).symm
  have hs : Commute (elementaryInclusion P x) (shortSplit P 0 1) := by
    simpa only [shortElementary_val] using hcomm (shortElementary P hp 0 1)
      (short_mem P hp .central 0 trivial 1)
  have hl (i : Fin 3) (hi : i ≠ 0) :
      Commute (elementaryInclusion P x) (longSplit P i 1) := by
    simpa only [longElementary_val] using hcomm (longElementary P hp i 1)
      (long_mem P hp .central i hi 1)
  have hlong (j : Fin 2) :
      Commute (elementaryInclusion P x) (curve P (![10,11] j) 1) := by
    fin_cases j
    · exact hl 1 (by decide)
    · exact hl 2 (by decide)
  have ht := central_fullLevi_mem_torus P hp (elementaryInclusion P x) hx hlong
  have hx1 := torus_eq_one_of_test_roots P hp (elementaryInclusion P x) ht hs (hlong 1)
  exact elementaryInclusion_injective P
    (hx1.trans (map_one (elementaryInclusion P)).symm)

/-- The full central Levi acts faithfully on its genuine root radical, including
the binary endpoint. The two long-root tests force a torus element, and the
short-root and highest-root weights force that torus element to be identity. -/
public theorem fullLeviRadicalAction_injective_central (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (fullLeviRadicalAction P .central) := by
  apply (injective_iff_map_eq_one _).mpr
  intro c hc
  have hk : c ∈ (fullLeviRadicalAction P .central).ker := hc
  rw [fullLeviRadicalAction_ker] at hk
  change c.val ∈ Subgroup.centralizer (radical P .central : Set (Carrier P)) at hk
  obtain ⟨x, hx, hxc⟩ := c.property
  have hk' : toCarrier P x ∈ Subgroup.centralizer (radical P .central : Set (Carrier P)) :=
    hxc.symm ▸ hk
  have hx1 := elementary_centralizer_eq_one P hp x hx hk'
  apply Subtype.ext
  change c.val = 1
  exact hxc.symm.trans ((congrArg (toCarrier P) hx1).trans (map_one _))

end
end Triality.Standard.Parabolics
