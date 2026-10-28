module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectedTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianStrongBounds

/-!
# Selected torus rank bounds on the original chosen Hermitian orbit

The original r ≥ 4n theorem supplies the selected actor's fixed-codimension
bound without an extra geometry hypothesis. The torus argument therefore
excludes n < k < 2n on the literal chosen automizer, conditional only on
its original fixed subgroup, preserved parabolic and rank-one module degree.
The existing half-field tensor coordinate theorem supplies this marking.

At k = 2n the constructed torus has fixed rank 3n, while its elementary
actor has rank and fixed rank 4n. The restricted coefficient estimate
makes this torus an odd GL₃ congruence on the very same coordinates.
The determinant-form calculation excludes this endpoint, including n = 1.
The original E.2.14(7,9), selection and local hypotheses stay explicit.
The full ambient exclusion and separate field-four endgame remain open.

Source: Aschbacher–Smith 8.2.2–3 and H.4.4(4), printed pp.715–716
and381 (1 March 2004 manuscript, refs/quasithin.pdf).
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

/-- The selected-rank argument and the previously proved r-bound remove
all rank and large-actor inputs from the literal intermediate-torus argument. -/
theorem sourceOrbit_hermitian_selected_not_intermediate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (x : Automizer D.sourceOrbit) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup D.sourceOrbit (zpowers x) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hp : PreservesMaximalParabolic n
      (coordinateHom (automizerRepresentation D.sourceOrbit) n
        (D.hermitianOrbitCoordinates n d) x))
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hc : coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d) x = (j x).val := by
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  exact Chapter8.Section02.HermitianSource.selected_not_intermediate_of_torus s n
    (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)
    x ho hfixed (hc ▸ hp) hd hnk hkn

/-- The constructed endpoint torus is an odd congruence on the original
chosen orbit; the actor fixed space and torus fixed space have ranks 4n and
3n respectively. This retains both earlier E.2.14 clauses explicitly. -/
theorem sourceOrbit_hermitian_selected_endpoint_congruence
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^(2*n)-1 ∧
      automizerFixedGroup D.sourceOrbit (zpowers x) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) = 3*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation D.sourceOrbit)
        (inducedAutomizer D.sourceOrbit A)) = 4*n ∧
      ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
        binaryCongruence n g = coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d) x ∧ Odd (orderOf g) := by
  obtain ⟨x,hx,ho,_,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s
    (by have hn := NeZero.pos n; omega)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  obtain ⟨ha,hxf,haf,_⟩ := Chapter8.Section02.HermitianSource.selected_endpoint_plane
    KnownSimple.IsKnownSimple eR h28 hchar hTI s n hkn
    (D.hermitianOrbitCoordinates n d) j hj he x hf
  obtain ⟨_,g,hg,hgo⟩ := Chapter8.Section02.HermitianSource.selected_endpoint_congruence
    KnownSimple.IsKnownSimple eR h28 hchar hTI s n hkn
    (D.hermitianOrbitCoordinates n d) j hj he x ho hx hf
  refine ⟨x,hx,hkn ▸ ho,hf,ha,hxf,haf,g,?_,hgo⟩
  rw [hg]
  apply LinearEquiv.ext
  intro v
  rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
  rfl

/-- The original selected torus cannot have k = 2n, including n = 1.
Only the earlier E.2.14 and local selection inputs remain explicit. -/
theorem sourceOrbit_hermitian_selected_not_endpoint
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) : False := by
  obtain ⟨x,hx,ho,_,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s
    (by have hn := NeZero.pos n; omega)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.selected_not_endpoint_of_torus
    KnownSimple.IsKnownSimple eR h28 hchar hTI s n hkn
    (D.hermitianOrbitCoordinates n d) j hj he x ho hx hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
