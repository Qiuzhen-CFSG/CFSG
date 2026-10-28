module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSaturatedTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianTorusBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWeakClosure

/-!
# Saturation and determinant norm on the original chosen orbit

The original Hermitian w and r bounds supply the inputs to the saturated
selected-offender calculation. Endpoint and intermediate torus exclusions
also squeeze the selected parameter to n, retaining their precise E.2.14,
local selection, parabolic and degree premises. The same original automizer
torus is transported to an odd congruence, and its determinant norm is
computed after the inner conjugation marking the actor as the plane radical.
The subsequent exclusion module supplies the literal half-field tensor consumer.

These are conditional source deductions. Constructing the selection,
discharging E.2.14 and the remaining intermediate premises, and the separate
field-four endgame remain open. The ambient determinant obstruction is applied
in the subsequent selected-torus exclusion module.
No conclusion excluding n = 1 is asserted.

Source: Aschbacher–Smith 8.2.2–4, printed pp.714–716, using H.4.4,
printed p.381 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The two selected-torus exclusions squeeze k to n on the original orbit.
The only numerical input is the earlier upper bound k ≤ 2n; the lower
bound for w is proved from the original source hypotheses. -/
theorem sourceOrbit_hermitian_selected_parameter
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ 2*n)
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k)
    (hp : ∀ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) →
      orderOf x = 2^k-1 →
      automizerFixedGroup D.sourceOrbit (zpowers x) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom →
      PreservesMaximalParabolic n (coordinateHom (automizerRepresentation D.sourceOrbit) n
        (D.hermitianOrbitCoordinates n d) x)) :
    k = n ∧ globalW D.sourceOrbit T = n ∧ IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ⊓ centralizer (D.sourceOrbit : Set G) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  have hkn : k ≤ n := by
    by_contra! hnk
    by_cases he : k = 2*n
    · exact D.sourceOrbit_hermitian_selected_not_endpoint h.toHypothesis1221
        eR eT h28 hchar hTI s n he d
    · obtain ⟨x,hx,ho,_,hf⟩ :=
        D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s (by omega)
      exact D.sourceOrbit_hermitian_selected_not_intermediate h hmany hV hnon s n d
        B eQ hfield hn x ho hf (hp x hx ho hf) hd hnk (by omega)
  exact Chapter8.Section02.HermitianSource.selected_hermitian_parameters s
    D.sourceOrbit_weakClosure_setup n
    (D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn) hkn

/-- The original source bounds discharge w, r and the large-actor geometry
in the selected fixed-subgroup calculation for n > 1. -/
theorem sourceOrbit_hermitian_selected_saturated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    k = n ∧ globalW D.sourceOrbit T = n ∧ IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      A = offenderNormalizer D.sourceOrbit i.val⁻¹ ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4*n ∧ rank U = 4*n ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ ((5*n : ℕ) : ℕ∞) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.selected_saturated_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn) hk
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)

/-- The same selected torus is an odd congruence fixing exactly the
canonical plane fixed space. Selection and E.2.14(9) stay explicit. -/
theorem sourceOrbit_hermitian_selected_saturated_torus
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let f := coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d)
    ∃ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^n-1 ∧
      automizerFixedGroup D.sourceOrbit (zpowers x) = D.sourceOrbit ⊓ centralizer (A : Set G) ∧
      fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x) =
        fixedSpace (automizerRepresentation D.sourceOrbit) (inducedAutomizer D.sourceOrbit A) ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) = 4*n ∧
      (∃ c : Cover n, ((inducedAutomizer D.sourceOrbit A).map f).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n) ∧
      IsFixedFieldLinear n (f x) ∧
      ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
        binaryCongruence n g = f x ∧ Odd (orderOf g) := by
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  obtain ⟨hkn,_,_,_,_,_,_,hU,_,_,_,_⟩ :=
    D.sourceOrbit_hermitian_selected_saturated h hmany hV hnon s n d B eQ hfield hn hk
  obtain ⟨x,hx,ho,_,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s
    (by omega)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hc : (binaryNormalizer n).subtype.comp j =
      coordinateHom (automizerRepresentation D.sourceOrbit) n (D.hermitianOrbitCoordinates n d) := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨hspace,hrank,hplane,hlin,g,hg,hgo⟩ :=
    Chapter8.Section02.HermitianSource.selected_saturated_torus_congruence s
      D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
      hw hk hr x hx ho hf
  change IsFixedFieldLinear n (((binaryNormalizer n).subtype.comp j) x) at hlin
  change binaryCongruence n g = ((binaryNormalizer n).subtype.comp j) x at hg
  rw [hc] at hplane hlin hg
  exact ⟨x,hx,hkn ▸ ho,hf.trans hU.symm,hspace,hrank,hplane,hlin,g,hg,hgo⟩

/-- The actual source torus has a nontrivial determinant norm after the
same inner conjugation that marks its actor as the plane radical. -/
theorem sourceOrbit_hermitian_selected_torus_det_norm_order
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let f := coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d)
    ∃ (x : Automizer D.sourceOrbit) (c : Cover n)
      (g : Matrix.GeneralLinearGroup (Fin 3) (E n)),
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^n-1 ∧
      ((inducedAutomizer D.sourceOrbit A).map f).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n ∧
      binaryCongruence n g = (MulAut.conj (binaryActionHom n c)) (f x) ∧
      Odd (orderOf g) ∧ orderOf (g.val.det * sigma n g.val.det) = 2^n-1 ∧
      g.val.det * sigma n g.val.det ≠ 1 := by
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  obtain ⟨hkn,_,_,_,_⟩ := Chapter8.Section02.HermitianSource.selected_hermitian_parameters
    s D.sourceOrbit_weakClosure_setup n hw hk
  obtain ⟨x,hx,ho,_,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s
    (by omega)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hc : (binaryNormalizer n).subtype.comp j =
      coordinateHom (automizerRepresentation D.sourceOrbit) n (D.hermitianOrbitCoordinates n d) := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨c,g,hplane,hg,hgo,hdord,hdet⟩ :=
    Chapter8.Section02.HermitianSource.selected_saturated_torus_det_norm_order s
      D.sourceOrbit_weakClosure_setup n hn (D.hermitianOrbitCoordinates n d) j hj he
      hw hk hr x hx ho hf
  change binaryCongruence n g = (MulAut.conj (binaryActionHom n c))
    (((binaryNormalizer n).subtype.comp j) x) at hg
  rw [hc] at hplane hg
  exact ⟨x,c,g,hx,hkn ▸ ho,hplane,hg,hgo,hdord,hdet⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
