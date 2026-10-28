module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSaturatedTorus
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Ambient

/-!
# The ambient contradiction for the saturated Hermitian torus

The original chosen-orbit normalizer is a two-local SQTK group. Its literal
surjection to the automizer, followed by the tensor coordinates and the same
plane conjugation, is the covering map in the split-determinant obstruction.
The original component marking puts the full special-linear image in its range.
Thus the saturated selected torus is impossible for n > 1, with no extra
scalar or quotient-rank assumption. The final wrapper constructs the coordinates
from the original half-field tensor input.

Selection, E.2.14(9), its local context and k <= n remain explicit. The earlier
parameter-squeeze theorem removes the last premise given its precise geometric
and E.2.14 inputs. These source inputs and the separate n = 1 endgame remain
obligations of the full Hermitian exclusion.

Source: Aschbacher–Smith 8.2.4, printed p.716, using H.4.4(5) and A.1.31(1),
printed pp.381 and27–28 (1 March 2004 manuscript, refs/quasithin.pdf).
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
private theorem tensor_coordinates_nonempty_for_exclusion
    {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) A U) (Q : Subgroup A)
    (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (B : BinaryField) (C : LinearCover B 3 Q) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible ρ C hs.irreducible
      schurDegree (inflated ρ C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible ρ C hs.irreducible
      HasAbsoluteTwistedModel (inflated ρ C) n) :
    Nonempty (ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n))) :=
  ⟨(Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates (ρ := ρ) (Q := Q) hs B C n hdegree hfield hmodel).choose⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The actual ambient normalizer excludes the saturated selected torus for
n > 1. Odd-prime ranks stay on that original two-local covering group. -/
theorem sourceOrbit_hermitian_selected_saturated_excluded
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
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ n) : False := by
  obtain ⟨x,c,g,_,_,_,hg,_,hord,_⟩ :=
    D.sourceOrbit_hermitian_selected_torus_det_norm_order h hmany hV hnon
      eT h28 hchar hTI s n d B eQ hfield hn hk
  let f₀ := coordinateHom (automizerRepresentation D.sourceOrbit) n
    (D.hermitianOrbitCoordinates n d)
  obtain ⟨j,hj,he,hmark⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hc : (binaryNormalizer n).subtype.comp j = f₀ := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  have hinner₀ : binaryImage n ≤ f₀.range := by
    intro a ha
    obtain ⟨q,hq⟩ := d.groupEquiv.surjective ⟨a,ha⟩
    obtain ⟨l,hl⟩ := D.orbitComponentHom_surjective q
    refine ⟨D.hermitianComponentAutomizer l,?_⟩
    rw [←hc]
    change (j (D.hermitianComponentAutomizer l)).val = a
    exact (hmark l).trans (congrArg Subtype.val ((congrArg d.groupEquiv hl).trans hq))
  let N := normalizer (D.sourceOrbit : Set G)
  let qN : N →* Automizer D.sourceOrbit := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  have hqN : Function.Surjective qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  let u := binaryActionHom n c
  let z := (MulAut.conj u).toMonoidHom
  let f : N →* BinaryAut n := z.comp (f₀.comp qN)
  have hu : u ∈ binaryImage n := ⟨c,rfl⟩
  have hinner : binaryImage n ≤ f.range := by
    intro a ha
    have ha' : u⁻¹*a*u ∈ binaryImage n :=
      (binaryImage n).mul_mem ((binaryImage n).mul_mem ((binaryImage n).inv_mem hu) ha) hu
    obtain ⟨b,hb⟩ := hinner₀ ha'
    obtain ⟨v,hv⟩ := hqN b
    refine ⟨v,?_⟩
    change u * f₀ (qN v) * u⁻¹ = a
    rw [hv,hb]
    simp [mul_assoc]
  have hgim : binaryCongruence n g ∈ f.range := by
    obtain ⟨v,hv⟩ := hqN x
    refine ⟨v,?_⟩
    change z (f₀ (qN v)) = binaryCongruence n g
    rw [hv]
    exact hg.symm
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    h.toHypothesis1221.simpleQTKE.twoLocal_sqtk
      ⟨D.sourceOrbit,D.sourceOrbit_weakClosure_setup.nontrivial,
        IsElementaryAbelian.isPGroup 2 D.sourceOrbit,rfl⟩
  exact no_split_det_norm_in_rank_two_cover n f hinner hN.stronglyQuasithin g hgim hord hn

/-- The endpoint, intermediate and saturated branches exhaust the selected
parameter range. The precise earlier source inputs remain explicit. -/
theorem sourceOrbit_hermitian_selected_excluded
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
        (D.hermitianOrbitCoordinates n d) x)) : False := by
  have hkn := (D.sourceOrbit_hermitian_selected_parameter h hmany hV hnon
    eR eT h28 hchar hTI s n d B eQ hfield hn hk hd hp).1
  exact D.sourceOrbit_hermitian_selected_saturated_excluded h hmany hV hnon
    eT h28 hchar hTI s n d B eQ hfield hn hkn.le

/-- The literal half-field tensor supplies the coordinates for the ambient
selected-torus contradiction. Earlier selection inputs remain explicit. -/
theorem sourceOrbit_hermitian_tensor_selected_saturated_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) (hk : k ≤ n) : False := by
  have hd : Nonempty (ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :=
    tensor_coordinates_nonempty_for_exclusion (A := D.orbitActor) (U := D.orbitSpace)
      D.orbitRepresentation D.orbitComponent hs B C n hdegree hfield hmodel
  let d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)) := Classical.choice hd
  exact D.sourceOrbit_hermitian_selected_saturated_excluded h hmany hV hnon
    eT h28 hchar hTI s n d B eQ hfield hn hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
