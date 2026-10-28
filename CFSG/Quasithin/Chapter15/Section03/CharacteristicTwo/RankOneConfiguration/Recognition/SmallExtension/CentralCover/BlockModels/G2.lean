module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Models
public import Theory.Representation.FirstCohomologyG2Natural.BinaryBound
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction

/-!
# Cubic cocycle tests in the binary G₂ line parabolic

The natural coefficients are trace-zero octonions modulo the scalar identity
line for the actual derived octonion automorphism group. Two cubic elements
of the restricted short-root parabolic detect octonion displacement modulo
scalars. The existing seven-coordinate cocycle bound then proves detection
of all cocycles under its explicit generating-pair premise. Faithfulness
uses the checked simplicity theorem and a nontrivial natural action.

This module does not claim that the generating-pair premise is proved.
Its owner is qt-i01-g2-binary-pair-generation. It also keeps the actual line
parabolic separate from the other parabolic, which has natural fixed vectors.

Source: Aschbacher--Smith, I.1.5--6 and I.2.3, printed pp.408 and 413,
and 15.3.31, printed p.1132. The imported split-octonion model and root
coordinates come from the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
namespace G2
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.BinaryParabolicPair

abbrev Actor := commutator (Model (ZMod 2))
abbrev Coefficients := Space (ZMod 2)
abbrev action : Representation (ZMod 2) Actor Coefficients := derivedAction (ZMod 2)

/-- The cubic in the short-root, line-stabilizing parabolic. -/
def cubicOne : Actor := ⟨cubicActor, cubicActor_mem_derived⟩

/-- A second cubic in the same parabolic, with the same coefficient marking. -/
def cubicTwo : Actor :=
  ⟨(rootB 1) * cubicActor * (rootB 1)⁻¹,
    (inferInstance : Actor.Normal).conj_mem _ cubicActor_mem_derived _⟩

theorem cubicOne_cube : cubicOne ^ 3 = 1 := Subtype.ext cubicActor_cube

theorem cubicTwo_cube : cubicTwo ^ 3 = 1 := by
  apply Subtype.ext
  change ((rootB (1 : ZMod 2)) * cubicActor * (rootB 1)⁻¹) ^ 3 = 1
  rw [conj_pow, cubicActor_cube]
  simp

private theorem scalar_of_two_displacements : ∀ x : Carrier (ZMod 2),
    binaryOffDiagonal (ZMod 2) (cubicOne.val.val x - x) = 0 →
    binaryOffDiagonal (ZMod 2) (cubicTwo.val.val x - x) = 0 →
    ∃ a : ZMod 2, a • unit = x := by decide +kernel

/-- The two cubics detect the octonion displacement construction, including
its scalar and principal parts. -/
theorem ambientCocycle_eq_zero_of_cubics (x : Carrier (ZMod 2))
    (h₁ : (ambientCocycle (ZMod 2) x).val cubicOne = 0)
    (h₂ : (ambientCocycle (ZMod 2) x).val cubicTwo = 0) :
    ambientCocycle (ZMod 2) x = 0 := by
  apply (ambientCocycle_eq_zero_iff _ _).mpr
  apply scalar_of_two_displacements x
  · have ht := congrArg (binaryCoordinates (ZMod 2)) h₁
    change binaryCoordinates (ZMod 2) (mk (ZMod 2) (displacement (ZMod 2) cubicOne.val x)) = _ at ht
    rw [binaryCoordinates_mk, map_zero] at ht
    exact ht
  · have ht := congrArg (binaryCoordinates (ZMod 2)) h₂
    change binaryCoordinates (ZMod 2) (mk (ZMod 2) (displacement (ZMod 2) cubicTwo.val x)) = _ at ht
    rw [binaryCoordinates_mk, map_zero] at ht
    exact ht

/-- Generation is the precise outstanding input in the existing binary
cohomology calculation. Under that input, the two parabolic cubics detect
all cocycles, with no fixed-vector or centralizer-recognition premise. -/
theorem detectedOn_of_cubics
    (hgen : closure ({binaryA (ZMod 2), binaryB (ZMod 2)} : Set Actor) = ⊤)
    (B : Subgroup Actor) (h₁ : cubicOne ∈ B) (h₂ : cubicTwo ∈ B) :
    DetectedOn action B := by
  intro f hf
  obtain ⟨x,rfl⟩ := ambientCocycle_surjective_of_binary_generation (ZMod 2) hgen f
  exact ambientCocycle_eq_zero_of_cubics x (hf _ h₁) (hf _ h₂)

/-- Cubic order puts each of the marked elements in the source O^{3′}
residual of any parabolic containing them. -/
theorem detectedOn_residual_of_cubics
    (hgen : closure ({binaryA (ZMod 2), binaryB (ZMod 2)} : Set Actor) = ⊤)
    (P : Subgroup Actor) (h₁ : cubicOne ∈ P) (h₂ : cubicTwo ∈ P) :
    DetectedOn action ((primeToResidual 3 P).map P.subtype) := by
  apply detectedOn_of_cubics hgen
  · refine ⟨⟨cubicOne,h₁⟩, mem_primeToResidual_of_pow (n := 1) ?_, rfl⟩
    apply Subtype.ext
    simpa using cubicOne_cube
  · refine ⟨⟨cubicTwo,h₂⟩, mem_primeToResidual_of_pow (n := 1) ?_, rfl⟩
    apply Subtype.ext
    simpa using cubicTwo_cube

/-- Both cubic tests belong to the actual restricted short-root parabolic. -/
theorem cubics_mem_firstParabolic : cubicOne ∈ derivedFirst ∧ cubicTwo ∈ derivedFirst := by
  refine ⟨cubicActor_mem, ?_⟩
  have hb : (rootB (1 : ZMod 2)) ∈ firstParabolic :=
    unipotent_le_firstParabolic (subset_closure (by simp))
  exact firstParabolic.mul_mem (firstParabolic.mul_mem hb cubicActor_mem)
    (firstParabolic.inv_mem hb)

/-- Marked detection in the actual G₂(2)' line parabolic, conditional only
on the concrete generation theorem needed by the binary cocycle bound. -/
theorem detectedOn_firstParabolic_residual
    (hgen : closure ({binaryA (ZMod 2), binaryB (ZMod 2)} : Set Actor) = ⊤) :
    DetectedOn action ((primeToResidual 3 derivedFirst).map derivedFirst.subtype) :=
  detectedOn_residual_of_cubics hgen _ cubics_mem_firstParabolic.1 cubics_mem_firstParabolic.2

private def testVector : TraceZero (ZMod 2) :=
  ⟨![1,0,0,0,0,0,0,0], by change trace _ = 0; decide +kernel⟩

/-- The actual six-dimensional action of G₂(2)' is faithful. -/
theorem faithful : Function.Injective action := by
  let : IsSimpleGroup Actor := isSimple_commutator_binary
  apply (MonoidHom.ker_eq_bot_iff action).mp
  rcases (inferInstance : action.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hb : action (binaryB (ZMod 2)) = 1 := by
      change binaryB (ZMod 2) ∈ action.ker
      rw [h]
      trivial
    have he := congrArg (fun t : Module.End (ZMod 2) Coefficients =>
      binaryCoordinates (ZMod 2) (t (mk (ZMod 2) testVector)) 0) hb
    change binaryCoordinates (ZMod 2)
      (derivedAction (ZMod 2) (binaryB (ZMod 2)) (mk (ZMod 2) testVector)) 0 =
      binaryCoordinates (ZMod 2) (mk (ZMod 2) testVector) 0 at he
    simp [binaryCoordinates_mk, binaryB_apply, testVector] at he

end G2
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
