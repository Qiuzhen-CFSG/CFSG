module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceRadicals

/-!
# The Hermitian plane offender on the original chosen orbit

The canonical coordinate homomorphism conjugates the actual automizer
representation by the descended chosen-orbit equivalence. Under the
preceding source saturation premises, the image of the literal offender
is conjugate to the marked plane root group, including half-degree one.
If that offender lies in the original Sylow subgroup, uniqueness of this
actor inside two-subgroups proves that its fixed subgroup is normal there.
The two-conjugate join centralizes that same fixed subgroup.

Finite w independently supplies an offender inside the original T. The
canonical kernel identity must still be supplied for the relevant source
configuration; this existence assertion does not silently assert it.
The final wrapper descends the actual half-field tensor input before
applying the result. The remaining weak-closure, H.4.4(3–5), canonical
kernel and field-four centralizer obligations stay with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith 8.2.4–5, printed pp.716–717; E.3.27–28,
printed pp.236–237; H.4.4, printed p.381 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE
open ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

include d in
/-- The plane root group is the image of the actual chosen-orbit offender,
under an equivariant embedding of the whole original automizer. -/
theorem sourceOrbit_hermitian_offender_plane
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T = n) (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit)
    (hkernel : offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :
    ∃ c : Cover n,
      ((inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map
        (ChapterK.Linear.Recognition.coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d))).map
            (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.offender_plane_coordinates
    D.sourceOrbit T n (D.hermitianOrbitCoordinates n d) j hj he hgeometry g
    D.sourceOrbit_weakClosure_setup hOff hw hr hkernel

include d in
/-- Relative normality in the original T and centralization by the actual
join follow from the marked actor, without an image-normalization callback. -/
theorem sourceOrbit_hermitian_offender_fixed_normal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T = n) (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit)
    (hkernel : offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    U = offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤
        centralizer (U : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.offender_fixed_normal_of_coordinates
    D.sourceOrbit T n (D.hermitianOrbitCoordinates n d) j hj he hgeometry g
    D.sourceOrbit_weakClosure_setup hOff hw hr hkernel hAT

omit d [NeZero n] in
/-- A finite weak-closure parameter supplies an actual offender inside the
original Sylow subgroup. The canonical kernel must still be established
for the selected source configuration. -/
theorem sourceOrbit_hermitian_exists_offender (hw : globalW D.sourceOrbit T = n) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧ offenderNormalizer D.sourceOrbit g ≤ T :=
  Chapter8.Section02.HermitianSource.exists_offender_le_sylow D.sourceOrbit_weakClosure_setup hw

omit d in
/-- The half-field tensor on the original inflated action supplies the
coordinates; the remaining hypotheses are the earlier source saturation
premises. No change of the Sylow subgroup or the chosen action is made. -/
theorem sourceOrbit_hermitian_tensor_fixed_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T = n) (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit)
    (hkernel : offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    U = offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤
        centralizer (U : Set G) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_offender_fixed_normal n d h.toHypothesis1221
    hgeometry g hOff hw hr hkernel hAT

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
