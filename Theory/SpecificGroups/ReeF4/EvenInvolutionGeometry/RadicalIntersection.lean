module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.Centrality
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.Bruhat
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Normality
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic

/-!
# Long-root saturation in the Ree parabolic radicals

A conjugate of the actual additive curve y₅ meets either specified parabolic
radical trivially or lies entirely in it. Bruhat factorization removes the
right positive factor by centrality of y₅ and the left positive factor by
relative normality of the radical.

For the remaining normalizer word n, conjugate a split torus action by n.
Its root permutation is the identity, so it preserves every radical generator
and hence the radical. The two split factors of y₅ have end-node characters
(1,0) and (0,1). Giving these nodes parameters c and c^θ sends y₅(t) to
y₅(ct). Thus one nonzero parameter in the radical gives every parameter.
The intermediate torus action need not preserve the fixed Ree group: its
input and output on this curve are the literal fixed matrices, and radical
membership is pulled back through the actual inclusion into the split group.

This proves the saturation input used in the Ree case of Aschbacher–Smith
E.1.14(1), printed p.214 of `refs/quasithin.pdf`, citing Aschbacher (1982),
Lemma 4.7, DOI 10.2307/2374202. The root and Bruhat conventions are GLS3
Table 2.4, 2.4.5(d), and 2.3.5, `refs/KGroup/GLS3/chapter2.tex`.
The proof also includes the binary endpoint m = 0.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
namespace ReeF4.EvenInvolutionGeometry.RadicalIntersection
open Parabolics LargeLocalSeeds
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations
open LocalBlockInput.PairRigidity.BlockParameters
open LocalBlockInput.PairNormalization.OppositionCell
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
noncomputable section

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]
private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private theorem long_four_val : (longRoot 4).val = ![1,-1,0,0] := by
  rw [longRoot_eq_sum]
  ext k; fin_cases k <;>
    norm_num [longRootCoefficients, typeF4SimpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem short_four_val : (shortRoot 4).val = ![0,1,0,0] := by
  ext k; fin_cases k <;>
    norm_num [shortRoot, longRoot, relativeRotation, middleReflection, endReflection,
      Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem high_four_val : (highRoot 4).val = ![1,1,0,0] := by
  rw [highRoot_eq_add_two 4 (by decide), long_four_val, short_four_val]
  ext k; fin_cases k <;> norm_num

private theorem mixed_four_val : (mixedRoot 4).val = ![1,0,0,0] := by
  rw [mixedRoot_eq_add 4 (by decide), long_four_val, short_four_val]
  ext k; fin_cases k <;> norm_num

private theorem high_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (highRoot 4) (typeF4SimpleRootIndex j) =
      if j = 0 then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [show (↑(typeF4RootPairing.pairingIn ℤ (highRoot 4)
    (typeF4SimpleRootIndex j)) : ℝ) =
      typeF4RootPairing.pairing (highRoot 4) (typeF4SimpleRootIndex j) from
        typeF4RootPairing.algebraMap_pairingIn ℤ _ _]
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot, high_four_val,
    typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.ext_iff]

private theorem mixed_pairing (j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (mixedRoot 4) (typeF4SimpleRootIndex j) =
      if j = 3 then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [show (↑(typeF4RootPairing.pairingIn ℤ (mixedRoot 4)
    (typeF4SimpleRootIndex j)) : ℝ) =
      typeF4RootPairing.pairing (mixedRoot 4) (typeF4SimpleRootIndex j) from
        typeF4RootPairing.algebraMap_pairingIn ℤ _ _]
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot, mixed_four_val,
    typeF4SimpleRootIndex_val]
  fin_cases j <;> norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, Fin.ext_iff]

private def scalingParameters (m : ℕ) (c : (CoefficientField m)ˣ) : TorusParameters m :=
  fun q => (![c, 1, 1, Units.map (rootFieldEnd m (longRoot 4)) c] :
    Fin 4 → (CoefficientField m)ˣ) (typeF4RootPairing_baseEquiv.symm q)

private theorem scaling_high (m : ℕ) (c : (CoefficientField m)ˣ) :
    rootScale (scalingParameters m c) (highRoot 4) = c := by
  rw [rootScale, integralChevalleyRootScale, ← typeF4RootPairing_baseEquiv.prod_comp]
  simp only [typeF4RootPairing_baseEquiv_val, high_pairing,
    scalingParameters, Equiv.symm_apply_apply]
  simp

private theorem scaling_mixed (m : ℕ) (c : (CoefficientField m)ˣ) :
    rootScale (scalingParameters m c) (mixedRoot 4) =
      Units.map (rootFieldEnd m (longRoot 4)) c := by
  rw [rootScale, integralChevalleyRootScale, ← typeF4RootPairing_baseEquiv.prod_comp]
  simp only [typeF4RootPairing_baseEquiv_val, mixed_pairing,
    scalingParameters, Equiv.symm_apply_apply]
  simp

private theorem scaling_centralWord (m : ℕ) (c : (CoefficientField m)ˣ)
    (t : CoefficientField m) :
    splitTorusConj (scalingParameters m c) (centralWord m 4 t) =
      centralWord m 4 (c * t) := by
  simp only [centralWord, map_mul, splitTorusConj_root, scaling_high, scaling_mixed,
    Units.coe_map, MonoidHom.coe_coe]

private theorem transported_torus_preserves_radical {m : ℕ} {n : SplitGroup m}
    (a : RootTransport n) (u : TorusParameters m) (s : Side)
    {x : SplitGroup m} (hx : x ∈ splitRadical m s) :
    (MulAut.conj n) (splitTorusConj u ((MulAut.conj n⁻¹) x)) ∈ splitRadical m s := by
  let f : MulAut (SplitGroup m) :=
    (MulAut.conj n⁻¹).trans ((splitTorusConj u).trans (MulAut.conj n))
  change f x ∈ _
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    change (MulAut.conj n) (splitTorusConj u
      ((MulAut.conj n⁻¹) (rootGeneratorInGroup m r t))) ∈ _
    rw [(NormalizerGeometry.rootTransport_inv a).conj_root, splitTorusConj_root,
      a.conj_root]
    simp only [NormalizerGeometry.rootTransport_inv, Equiv.apply_symm_apply]
    exact subset_closure ⟨r, _, hr, rfl⟩
  | one => simpa only [map_one] using (one_mem (splitRadical m s))
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using inv_mem hx

private theorem normalizer_parameter_saturation {m : ℕ} {n : SplitGroup m}
    (hn : n ∈ splitNormalizerWords m) (s : Side)
    {t : CoefficientField m} (ht : t ≠ 0)
    (hx : (MulAut.conj n) (centralWord m 4 t) ∈ splitRadical m s)
    (v : CoefficientField m) :
    (MulAut.conj n) (centralWord m 4 v) ∈ splitRadical m s := by
  by_cases hv : v = 0
  · subst v
    have hz : centralWord m 4 (0 : CoefficientField m) = 1 := by
      simp [centralWord, show ∀ r : F4Chevalley.Root, rootGeneratorInGroup m r 0 = 1 from
        fun r => Subtype.ext (F4Chevalley.rootCurve_zero r)]
    simp [hz]
  · let c : (CoefficientField m)ˣ := Units.mk0 (v / t) (div_ne_zero hv ht)
    obtain ⟨a⟩ := rootTransport_of_mem_splitNormalizerWords hn
    have h := transported_torus_preserves_radical a (scalingParameters m c) s hx
    have he : (MulAut.conj n⁻¹) ((MulAut.conj n) (centralWord m 4 t)) =
        centralWord m 4 t := by simp only [MulAut.conj_apply]; group
    rw [he, scaling_centralWord] at h
    simpa only [c, Units.val_mk0, div_mul_cancel₀ _ ht] using h

/-- One nonzero point in a conjugated marked curve forces every point into
one of the actual Ree parabolic radicals. -/
theorem longRootElement_conj_mem_radical_of_ne_zero (m : ℕ) (g : Model m)
    (s : Side) {t : CoefficientField m} (ht : t ≠ 0)
    (hx : (MulAut.conj g) (longRootElement m t) ∈ radical m s)
    (v : CoefficientField m) :
    (MulAut.conj g) (longRootElement m v) ∈ radical m s := by
  obtain ⟨u, hu, n, hn, w, hw, hg⟩ := Overlap.exists_fixed_normal_form m g
  have huN : u ∈ normalizer (radical m s : Set (Model m)) :=
    SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m s
      (borel_le_parabolic m s (unipotent_le_borel m hu))
  have he (a : CoefficientField m) :
      (MulAut.conj g) (longRootElement m a) =
        (MulAut.conj u) ((MulAut.conj n) (longRootElement m a)) := by
    have hc : (MulAut.conj w) (longRootElement m a) = longRootElement m a := by
      change w * longRootElement m a * w⁻¹ = _
      rw [← (longRootElement_commute_unipotent m a w hw).eq]
      simp only [mul_inv_cancel_right]
    rw [hg]
    calc
      _ = (MulAut.conj u) ((MulAut.conj n) ((MulAut.conj w)
          (longRootElement m a))) := by simp only [MulAut.conj_apply]; group
      _ = _ := by rw [hc]
  rw [he] at hx ⊢
  have hx' : (MulAut.conj n) (longRootElement m t) ∈ radical m s :=
    (mem_normalizer_iff.mp huN _).mpr hx
  apply (mem_normalizer_iff.mp huN _).mp
  change toSplitGroup m ((MulAut.conj n) (longRootElement m v)) ∈ splitRadical m s
  have hx'' : (MulAut.conj (toSplitGroup m n)) (centralWord m 4 t) ∈
      splitRadical m s := by
    change toSplitGroup m ((MulAut.conj n) (longRootElement m t)) ∈ splitRadical m s at hx'
    simpa only [MulAut.conj_apply, map_mul, map_inv, longRootElement_coe] using hx'
  simpa only [MulAut.conj_apply, map_mul, map_inv, longRootElement_coe] using
    normalizer_parameter_saturation hn s ht hx'' v

/-- A conjugate of the matrix-defined long-root group meets either parabolic
radical trivially or is contained in it. This also holds at the binary endpoint. -/
theorem longRootGroup_conj_le_radical_of_inf_ne_bot (m : ℕ) (g : Model m)
    (s : Side)
    (h : (longRootGroup m).map (MulAut.conj g).toMonoidHom ⊓ radical m s ≠ ⊥) :
    (longRootGroup m).map (MulAut.conj g).toMonoidHom ≤ radical m s := by
  obtain ⟨x, hx, hne⟩ :=
    ((longRootGroup m).map (MulAut.conj g).toMonoidHom ⊓ radical m s).bot_or_exists_ne_one
      |>.resolve_left h
  obtain ⟨y, hy, hxy⟩ := hx.1
  obtain ⟨t, rfl⟩ := (mem_longRootGroup m y).mp hy
  have ht : t ≠ 0 := by
    intro hz
    apply hne
    rw [← hxy, hz, longRootElement_zero, map_one]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := (mem_longRootGroup m y).mp hy
  exact longRootElement_conj_mem_radical_of_ne_zero m g s ht (hxy ▸ hx.2) v

end
end ReeF4.EvenInvolutionGeometry.RadicalIntersection
