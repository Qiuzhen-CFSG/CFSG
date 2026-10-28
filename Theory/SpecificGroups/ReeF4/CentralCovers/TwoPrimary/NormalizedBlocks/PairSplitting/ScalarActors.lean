module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.RootBlocks
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FixedTorus
-- This implementation calculation needs the concrete layout, whose body is
-- intentionally hidden. Keep the coupling local instead of exposing it upstream.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# Scalar actors on the four additive Ree blocks

Compute the four first-root characters on the compatible torus `blockTorus b 1`.
They are `b` on the first two blocks and `b * θ(b)^2` on the last two.
The identity `θ(θ(c))^2 = c` explicitly inverts the latter character.
The inverse diagonal matrix lies in the actual fixed group, and its conjugation
scales both coordinates of each paired root word. Transport through the genuine
fixed-group equivalence supplies an inner actor in `Model m` for every scalar.

Source: GLS3 §§2.3–2.4, especially Table 2.4 and 2.4.7, in
`refs/KGroup/GLS3/chapter2.tex`; the covering application is §6.1 and
Aschbacher–Smith I.1.1–4, printed pp.407–408.
-/

public section

open scoped BigOperators commutatorElement
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4
open ReeF4.CentralCovers.TwoPrimary
open ReeF4.Parabolics
open ReeF4.Parabolics.RadicalCoordinates
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open ReeF4.NormalizedRootCentralizers.CenterExponent
open ReeF4.ElementaryTwoBound ReeF4.ElementaryTwoBound.RootCalculations

noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.PairSplitting
open RootPairing.IntegralGeckConstruction

private def tab (n : Fin 24) : F4Chevalley.Root :=
  ⟨RootPartition.table n, RootPartition.table_mem n⟩

private theorem tab_simple (i : Fin 4) :
    tab (![0,8,9,1] i) = typeF4SimpleRootIndex i := by
  apply Subtype.ext
  ext k
  fin_cases i <;> fin_cases k <;>
    norm_num [tab, RootPartition.table, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem scale_add (m : ℕ) (u : TorusParameters m)
    (r s v : F4Chevalley.Root) (hv : v.val = r.val + s.val) :
    rootScale u v = rootScale u r * rootScale u s := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ v q =
      typeF4RootPairing.pairingIn ℤ r q + typeF4RootPairing.pairingIn ℤ s q :=
    typeF4RootPairing.pairingIn_eq_add_of_root_eq_add hv
  simp only [rootScale, integralChevalleyRootScale, hp, zpow_add, Finset.prod_mul_distrib]

private theorem pair_scale (m : ℕ) (b : (CoefficientField m)ˣ) (j : Fin 4) :
    rootScale (blockTorus b 1) (positiveRootWordLayout.blocks.roots (.inl (j,0))).val =
      (if j.val < 2 then b else b * Units.map (theta m) b ^ 2) := by
  let S := rootScale (blockTorus b 1)
  have hs (i : Fin 4) : S (tab (![0,8,9,1] i)) =
      ![b,1,1,Units.map (theta m) b] i := by
    rw [tab_simple]
    change rootScale (torusParametersOfSimpleScales _) (typeF4SimpleRootIndex i) = _
    simp only [rootScale_torusParametersOfSimpleScales, map_one]
  have h0 : S (tab 0) = b := hs 0
  have h8 : S (tab 8) = 1 := hs 1
  have h9 : S (tab 9) = 1 := hs 2
  have h1 : S (tab 1) = Units.map (theta m) b := hs 3
  have h10 : S (tab 10) = S (tab 8) * S (tab 9) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h11 : S (tab 11) = S (tab 9) * S (tab 10) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h16 : S (tab 16) = S (tab 0) * S (tab 8) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h2 : S (tab 2) = S (tab 11) * S (tab 16) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h7 : S (tab 7) = S (tab 1) * S (tab 2) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h4 : S (tab 4) = S (tab 1) * S (tab 7) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h3 : S (tab 3) = S (tab 1) * S (tab 11) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h5 : S (tab 5) = S (tab 0) * S (tab 3) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have h6 : S (tab 6) = S (tab 3) * S (tab 5) := by
    apply scale_add m (blockTorus b 1)
    ext k; fin_cases k <;>
      norm_num [tab, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  have hr : (positiveRootWordLayout.blocks.roots (.inl (j,0))).val =
      tab ⟨2*j.val, by omega⟩ := by
    apply Subtype.ext
    change ((rootBlocks .positive).roots (.inl (j,0))).val.val = _
    rw [rootBlocks_roots_val]
    rfl
  rw [hr]
  change S (tab _) = _
  fin_cases j <;> simp [h0,h1,h8,h9,h10,h11,h16,h2,h7,h4,h3,h5,h6,pow_two,
    mul_comm,mul_left_comm]

private theorem theta_units_twice_sq (m : ℕ) (c : (CoefficientField m)ˣ) :
    Units.map (theta m : CoefficientField m →* CoefficientField m)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) c) ^ 2 = c := by
  apply Units.ext
  change (theta m (theta m c.val)) ^ 2 = c.val
  simp only [theta_apply, ← pow_mul, ← pow_add]
  rw [show 2 ^ (m + m) * 2 = 2 ^ (2 * m + 1) by
    rw [pow_succ]; congr 2; omega]
  exact field_pow m c.val

private theorem exists_pair_scale (m : ℕ) (j : Fin 4) (c : (CoefficientField m)ˣ) :
    ∃ u : TorusParameters m, TwistCompatible u ∧
      rootScale u (positiveRootWordLayout.blocks.roots (.inl (j,0))).val = c := by
  by_cases hj : j.val < 2
  · exact ⟨blockTorus c 1, blockTorus_twistCompatible c 1,
      by rw [pair_scale, if_pos hj]⟩
  · let b := Units.map (theta m : CoefficientField m →* CoefficientField m) c ^ 2 * c⁻¹
    refine ⟨blockTorus b 1, blockTorus_twistCompatible b 1, ?_⟩
    rw [pair_scale, if_neg hj]
    dsimp only [b]
    simp only [map_mul, map_pow, map_inv, mul_pow, theta_units_twice_sq]
    simp [mul_comm, mul_left_comm, mul_assoc]
    group

private theorem pair_conj (m : ℕ) (j : Fin 4) (u : TorusParameters m) (hu : TwistCompatible u)
    (x : CoefficientField m) :
    let r := (positiveRootWordLayout.blocks.roots (.inl (j,0))).val
    let a := rootScale u r
    ∀ g : (canonicalLocalBlockInput m).fixedGroup, g.val.val = (torusMatrix u)⁻¹ →
    let z : Model m := (canonicalLocalBlockInput m).modelEquiv g
    z * pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j) (.ofAdd x) * z⁻¹ =
      pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j) (.ofAdd ((a : CoefficientField m) * x)) := by
  dsimp
  intro g hg
  let z : Model m := (canonicalLocalBlockInput m).modelEquiv g
  let r := (positiveRootWordLayout.blocks.roots (.inl (j,0))).val
  let a := rootScale u r
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv]
  change (toSplitGroup m z) * (toSplitGroup m (mainElement m (rootIndex (.inl j)) x)) *
      (toSplitGroup m z)⁻¹ = toSplitGroup m
        (mainElement m (rootIndex (.inl j)) ((rootScale u r : CoefficientField m) * x))
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
  apply Subtype.ext
  change g.val.val * (toSplitGroup m (mainElement m (rootIndex (.inl j)) x)).val * g.val.val⁻¹ =
    (toSplitGroup m (mainElement m (rootIndex (.inl j)) ((rootScale u r : CoefficientField m) * x))).val
  rw [hg]
  rw [mainElement_coe, mainElement_coe]
  change (torusMatrix u)⁻¹ * (rootWord m (positiveRootWordLayout.pairIndex j) x).val *
      (torusMatrix u)⁻¹⁻¹ =
    (rootWord m (positiveRootWordLayout.pairIndex j) ((rootScale u r : CoefficientField m) * x)).val
  have hw (y : CoefficientField m) :
      rootWord m (positiveRootWordLayout.pairIndex j) y =
        pairWord m (fun s => (positiveRootWordLayout.blocks.roots (.inl (j,s))).val)
          (pairSolution m y) := positiveRootWordLayout.pair_rootWord m j y
  rw [hw x, hw ((rootScale u r : CoefficientField m) * x)]
  change matrixTorusConj u (pairWord m
      (fun s => (positiveRootWordLayout.blocks.roots (.inl (j,s))).val) (pairSolution m x)).val = _
  rw [matrixTorusConj_apply]
  change (torusMatrix u)⁻¹ *
      (F4Chevalley.rootCurve r (pairSolution m x 0) *
        F4Chevalley.rootCurve (positiveRootWordLayout.blocks.roots (.inl (j,1))).val
          (pairSolution m x 1)) * torusMatrix u =
    F4Chevalley.rootCurve r ((rootScale u r : CoefficientField m) * x) *
      F4Chevalley.rootCurve (positiveRootWordLayout.blocks.roots (.inl (j,1))).val
        (pairSolution m ((rootScale u r : CoefficientField m) * x) 1)
  have hdual := positiveRootWordLayout.blocks.pair_dual j
  have hroot : ((positiveRootWordLayout.blocks.roots (.inl (j,1))).val) =
      exceptionalRootPermutation r := hdual.symm
  have hscale := hu r
  have hlong := positiveRootWordLayout.blocks.pair_long j
  have hscale0 : (rootScale u (exceptionalRootPermutation r) : CoefficientField m) =
      halfFrobenius m (a : CoefficientField m) := by
    rw [← hscale]
    rw [exceptionalParameter_of_long hlong]
    rfl
  calc
    _ = ((torusMatrix u)⁻¹ * F4Chevalley.rootCurve r (pairSolution m x 0) * torusMatrix u) *
        ((torusMatrix u)⁻¹ * F4Chevalley.rootCurve
          (positiveRootWordLayout.blocks.roots (.inl (j,1))).val (pairSolution m x 1) * torusMatrix u) := by group
    _ = _ := by
      rw [torusMatrix_conjugation, torusMatrix_conjugation, hroot, hscale0]
      simp [pairSolution, r, a, map_mul]

/-- Every nonzero scalar is conjugation by an actual element of the Ree model. -/
theorem exists_scalar_actor (m : ℕ) (j : Fin 4) (c : CoefficientField m) (hc : c ≠ 0) :
    ∃ z : Model m, ∀ x : CoefficientField m,
      z * pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j) (.ofAdd x) * z⁻¹ =
        pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j) (.ofAdd (c*x)) := by
  obtain ⟨u, hu, hs⟩ := exists_pair_scale m j (Units.mk0 c hc)
  obtain ⟨g,hg⟩ := exists_fixedGroup_torusMatrix_inv (canonicalLocalBlockInput m) u hu
  refine ⟨(canonicalLocalBlockInput m).modelEquiv g, fun x => ?_⟩
  simpa only [hs, Units.val_mk0] using pair_conj m j u hu x g hg

end ReeF4.CentralCovers.TwoPrimary.PairSplitting
