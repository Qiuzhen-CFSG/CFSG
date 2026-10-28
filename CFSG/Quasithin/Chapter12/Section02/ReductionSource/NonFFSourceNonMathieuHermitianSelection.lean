module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The selected canonical offender on the original Hermitian orbit

The selected E.2 pair uses the original T, N_G(L), orbit subgroup and
right conjugator. Its quotient parameter supplies the actor corank.
The preceding bounds n ≤ w and k ≤ n force k = w = n; minimality then
identifies the selected core actor with the offender normalizer and
supplies its kernel, without independent offender or kernel callbacks.

The tensor consumer first descends the actual inflated representation.
It then applies the normalizer embedding and the canonical-pair theorem
to give the 4n fixed subgroup, its relative normality in T and its
centralization by the selected I. Its ambient normalizer has characteristic
two by the original even-characteristic hypothesis. All statements retain
half-degree one.

Selection itself, n ≤ w, k ≤ n, r ≥ 4n and H.4.4(3) remain explicit;
these are not consequences of descent alone. Their proof and the source
exclusions for n > 1 and field four remain with
qt-d-1222-nonmathieu-hermitian-exclusion. This module does not claim
completion of 7.0.1 or 8.2.13.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 8.2.2–5
and the introduction to 8.2.2, printed pp.714–717 (refs/quasithin.pdf).
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

/-- The selected pair supplies the canonical offender and its exact kernel
on the original orbit, once its parameter is squeezed by the earlier bounds. -/
theorem sourceOrbit_hermitian_selected_offender
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n) :
    k = n ∧ globalW D.sourceOrbit T = n ∧ IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ⊓ centralizer (D.sourceOrbit : Set G) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  exact Chapter8.Section02.HermitianSource.selected_hermitian_parameters
    s D.sourceOrbit_weakClosure_setup n hw hk

/-- The original coordinate marking discharges the automizer transport in
the selected-pair saturation and fixed-subgroup theorem. -/
theorem sourceOrbit_hermitian_selected_fixed_subgroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
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
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.selected_hermitian_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
    hgeometry hw hk hr

/-- The literal half-field tensor supplies the coordinates used for the
canonical selected pair. The earlier bounds and large-actor estimate remain explicit. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
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
  exact D.sourceOrbit_hermitian_selected_fixed_subgroup h.toHypothesis1221 s n d
    hgeometry hw hk hr

/-- The next source local subgroup N_G(U) contains the original T and has
characteristic two; the selected I centralizes the same nontrivial U. -/
theorem sourceOrbit_hermitian_tensor_selected_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (hw : (n : ℕ∞) ≤ globalW D.sourceOrbit T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
    U ≠ ⊥ ∧ normalizer (U : Set G) ∈ Chapter1.HeOver G (T : Set G) ∧
      HasCharacteristicTwo (normalizer (U : Set G)) ∧ I ≤ centralizer (U : Set G) := by
  obtain ⟨_,_,_,_,_,_,_,hU,_,_,_,_,hTN,hIC⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_fixed_subgroup h hs s B C n
      hdegree hfield hmodel hgeometry hw hk hr
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  have hne : U ≠ ⊥ := by
    intro hz
    change rank U = 4*n at hU
    rw [hz, Representation.BinaryOffender.rank_bot] at hU
    have hn := NeZero.pos n
    omega
  have hUT : U ≤ T := inf_le_left.trans D.sourceOrbit_weakClosure_setup.le_sylow
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hne,T.isPGroup'.to_le hUT,rfl⟩
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.simpleQTKE.evenCharacteristic T) hlocal hTN
  exact ⟨hne,⟨hHe,Chapter1.mem_H_of_isTwoLocal hlocal,hTN⟩,
    Chapter1.mem_He_iff.mp hHe,hIC⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
