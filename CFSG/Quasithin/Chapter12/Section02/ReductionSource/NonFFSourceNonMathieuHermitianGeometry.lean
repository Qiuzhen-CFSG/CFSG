module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelection
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianRadicals

/-!
# The proved large-actor estimate on the original chosen orbit

The elementary fixed-space bound H.4.4(3), for actors of rank at least 3n,
now follows from the literal tensor geometry. The full automizer embeds
in its binary normalizer through the previously constructed coordinates.
This discharges the large-actor premise of the selected-offender saturation,
fixed subgroup and characteristic-two normalizer results, including n = 1.

The selected pair and the bounds n ≤ w, k ≤ n and r ≥ 4n remain explicit.
Their construction, H.4.4(4–5), and the field-four endgame through 8.2.13
remain with qt-d-1222-nonmathieu-hermitian-exclusion. These conditional
applications do not assert the full source exclusion.

Source: Aschbacher–Smith H.4.4(3), 8.2.4–5, printed pp.381,716–717
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- H.4.4(3) on the original full automizer, with the literal orbit action. -/
theorem sourceOrbit_hermitian_large_actor_fixedCodim
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (A : Subgroup (Automizer D.sourceOrbit)) [IsElementaryAbelian 2 A]
    (hr : 3*n ≤ rank A) :
    5*n ≤ fixedCodim (automizerRepresentation D.sourceOrbit) A := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  let : IsElementaryAbelian 2 (A.map j) := IsElementaryAbelian.map j
  have hm : 3*n ≤ rank (A.map j) := by rwa [rank_map_injective j hj]
  have hb := LargeActors.overgroup_large_elementary_fixedCodim n
    (binaryNormalizer n) le_rfl (A.map j) hm
  rwa [← fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
    (overgroupAction n (binaryNormalizer n)) j (D.hermitianOrbitCoordinates n d) he A] at hb

/-- The original coordinate marking discharges the automizer transport in
the selected-pair saturation and fixed-subgroup theorem. -/
theorem sourceOrbit_hermitian_selected_fixed_subgroup_of_bounds
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit) :
    let A := offenderNormalizer D.sourceOrbit i.val⁻¹
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    k = n ∧ globalW D.sourceOrbit T = n ∧ IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧ A ≤ T ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      ⁅⁅⁅D.sourceOrbit,A⁆,A⁆,A⁆ = ⊥ ∧ rank (inducedAutomizer D.sourceOrbit A) = 4*n ∧
      rank U = 4*n ∧ globalR D.sourceOrbit ≤ ((5*n : ℕ) : ℕ∞) ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) := by
  exact D.sourceOrbit_hermitian_selected_fixed_subgroup h s n d
    (fun A hA hrank => by
      let := hA.2
      exact LargeActors.overgroup_large_elementary_fixedCodim n (binaryNormalizer n)
        le_rfl A hrank) hw hk hr

/-- The same selected actor is the literal plane radical in the original
orbit coordinates; no fixed-space estimate or canonical-kernel premise remains. -/
theorem sourceOrbit_hermitian_selected_plane_of_bounds
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit) :
    ∃ c : Cover n,
      ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)).map
        (coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d))).map
            (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  obtain ⟨_,hew,hOff,_,hker⟩ := D.sourceOrbit_hermitian_selected_offender s n hw hk
  exact D.sourceOrbit_hermitian_offender_plane n d h (fun A hA hrank => by
    let := hA.2
    exact LargeActors.overgroup_large_elementary_fixedCodim n (binaryNormalizer n)
      le_rfl A hrank) i.val⁻¹ hOff hew hr hker

/-- The literal half-field tensor supplies the coordinates used for the
canonical selected pair. The earlier weak-closure bounds remain explicit. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup_of_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit) :
    let A := offenderNormalizer D.sourceOrbit i.val⁻¹
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    k = n ∧ globalW D.sourceOrbit T = n ∧ IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧ A ≤ T ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      ⁅⁅⁅D.sourceOrbit,A⁆,A⁆,A⁆ = ⊥ ∧ rank (inducedAutomizer D.sourceOrbit A) = 4*n ∧
      rank U = 4*n ∧ globalR D.sourceOrbit ≤ ((5*n : ℕ) : ℕ∞) ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_selected_fixed_subgroup_of_bounds h.toHypothesis1221 s n d
    hw hk hr

/-- The next source local subgroup N_G(U) contains the original T and has
characteristic two; the selected I centralizes the same nontrivial U. -/
theorem sourceOrbit_hermitian_tensor_selected_normalizer_of_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
    U ≠ ⊥ ∧ normalizer (U : Set G) ∈ Chapter1.HeOver G (T : Set G) ∧
      HasCharacteristicTwo (normalizer (U : Set G)) ∧ I ≤ centralizer (U : Set G) := by
  exact D.sourceOrbit_hermitian_tensor_selected_normalizer h hs s B C n
    hdegree hfield hmodel (fun A hA hrank => by
      let := hA.2
      exact LargeActors.overgroup_large_elementary_fixedCodim n (binaryNormalizer n)
        le_rfl A hrank) hw hk hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
