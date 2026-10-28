module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianParameters
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianActors

/-!
# The canonical Hermitian offender is in the original component image

Transport a large elementary subgroup of the actual ambient automizer into
the binary normalizer. The outer-centralizer bound puts that image inside
the Hermitian component. Surjectivity of the original map from L and
injectivity of the whole-automizer embedding then recover containment in
the literal conjugation image of L.

The offender application uses the checked rank saturation and includes
half-degree one. Its earlier weak-closure, canonical-kernel and H.4.4(3)
premises remain explicit. Their construction and the parabolic and
centralizer arguments remain with qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith H.4.4(3–6), 8.2.4–5, printed pp.381 and716
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

include d in
/-- Large elementary actors in the literal ambient automizer come from L. -/
theorem sourceOrbit_hermitian_large_actor_inner
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup (Automizer D.sourceOrbit)) [IsElementaryAbelian 2 A]
    (hsize : 2 * n + 1 < rank A) : A ≤ D.hermitianComponentAutomizer.range := by
  obtain ⟨j, hj, _, hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAN : A.map f ≤ binaryNormalizer n := by
    rintro _ ⟨a, _, rfl⟩
    exact (j a).property
  have hinner := large_elementary_le_image n (A.map f) hAN (by
    rwa [rank_map_injective f hf])
  intro a ha
  let x : binaryImage n := ⟨f a, hinner (mem_map_of_mem f ha)⟩
  obtain ⟨l, hl⟩ := (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective) x
  refine ⟨l, hf ?_⟩
  exact (hcomp l).trans (congrArg Subtype.val hl)

include d in
/-- Once the source saturation premises hold, the canonical offender lies
in the original component image even in the field-four case. -/
theorem sourceOrbit_hermitian_offender_inner
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3 * n ≤ rank A → 5 * n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T = n) (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit)
    (hkernel : offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :
    inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g) ≤
      D.hermitianComponentAutomizer.range := by
  have ha := (D.sourceOrbit_hermitian_offender_parameters n d h hgeometry g hOff hw hr hkernel).1
  let : IsElementaryAbelian 2
      (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) :=
    offender_inducedAutomizer_elementary D.sourceOrbit g
  apply D.sourceOrbit_hermitian_large_actor_inner n d h
  rw [ha]
  have hn := NeZero.pos n
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
