module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Local
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The actual PSL3(2) quotient of the marked M24 2A centralizer

The surjective natural action on the stabilizer of the marked vector is
followed by its action on the three-space modulo that vector. Its kernel
is exactly the specified preimage of the point radical. The first
isomorphism theorem and the binary GL3–PSL3 comparison give the quotient
isomorphism. Counting the two exact action sequences gives centralizer
order 21504 and kernel order 128. The kernel is also the intrinsic two-core.

Source: Aschbacher–Smith 16.1.5(7), printed p.1171; GLS3 Table 5.3e.
The dihedral central-product description remains a separate obligation.
-/

@[expose] public section
noncomputable section
open Subgroup
open Sporadic.Mathieu.M24ChapterHStabilizers
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

/-- The quotient of the natural four-space by the marked fixed line. -/
abbrev QuotientSpace := Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace markedVector

/-- The natural action, with codomain restricted to the full point stabilizer. -/
def pointAction : centralizer2A →*
    Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer markedVector :=
  linearAction.codRestrict _ (fun g => (fixes_markedVector_iff (toOctad g)).mpr g.property)

theorem pointAction_surjective : Function.Surjective pointAction := by
  intro a
  obtain ⟨g, hg⟩ := (show a.val ∈ linearAction.range by
    rw [linearAction_range]; exact a.property)
  exact ⟨g, Subtype.ext hg⟩

theorem pointAction_ker : pointAction.ker = translationKernel := by
  ext g
  rw [← linearAction_ker]
  change pointAction g = 1 ↔ linearAction g = 1
  exact Subtype.ext_iff

/-- Action on the literal quotient by the marked line. -/
def quotientAction : centralizer2A →* BinaryLinear.GL QuotientSpace :=
  (Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction markedVector).comp pointAction

theorem quotientAction_surjective : Function.Surjective quotientAction :=
  (Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_surjective markedVector).comp
    pointAction_surjective

theorem quotientAction_ker : quotientAction.ker = kernel := by
  ext g
  change pointAction g ∈ Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector ↔ _
  rw [Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff]
  change (∀ v, linearAction g v - v ∈ Submodule.span (ZMod 2) {markedVector}) ↔
    (∀ w ∈ Submodule.span (ZMod 2) {markedVector}, linearAction g w = w) ∧
      ∀ v, linearAction g v - v ∈ Submodule.span (ZMod 2) {markedVector}
  exact ⟨fun h => ⟨Theory.LinearAlgebra.BinaryFivePointStabilizer.fixes_line
    markedVector (pointAction g), h⟩, And.right⟩

theorem quotientSpace_finrank : Module.finrank (ZMod 2) QuotientSpace = 3 :=
  Theory.LinearAlgebra.BinaryFourPointStabilizer.quotient_finrank markedVector
    markedVector_ne_zero (by rw [Module.finrank_pi, Fintype.card_fin])

/-- Binary coordinates on the genuine quotient space. -/
def quotientCoordinates : QuotientSpace ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [quotientSpace_finrank, Module.finrank_pi, Fintype.card_fin])

/-- The actual quotient by the specified normal kernel is the matrix PSL3(2). -/
def quotientEquiv : (centralizer2A ⧸ kernel) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq quotientAction_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective quotientAction quotientAction_surjective).trans
      ((BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates).trans
        BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective))

/-- This is the group action whose quotient marking defines `quotientEquiv`. -/
theorem quotientEquiv_mk (g : centralizer2A) :
    quotientEquiv (QuotientGroup.mk' kernel g) =
      BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective
        (BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates (quotientAction g)) := rfl

theorem centralizer_card : Nat.card centralizer2A = 21504 := by
  have h := pointAction.ker.card_mul_index
  rw [pointAction_ker, translationKernel_card] at h
  have hi : translationKernel.index = 1344 := by
    rw [← pointAction_ker, index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        pointAction pointAction_surjective).toEquiv]
    exact Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer markedVector
      markedVector_ne_zero (by rw [Module.finrank_pi, Fintype.card_fin])
  rw [hi] at h
  omega

theorem kernel_card : Nat.card kernel = 128 := by
  have h := quotientAction.ker.card_mul_index
  rw [index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      quotientAction quotientAction_surjective).toEquiv,
    Theory.LinearAlgebra.BinaryFourPointStabilizer.card_linearGroup_three quotientSpace_finrank,
    quotientAction_ker, centralizer_card] at h
  omega

/-- The specified kernel is precisely the intrinsic two-core, with no extra two-part. -/
theorem kernel_eq_twoCore : kernel = pCore 2 centralizer2A := by
  let : Finite QuotientSpace := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL QuotientSpace) :=
    Finite.of_injective (fun a : BinaryLinear.GL QuotientSpace => (a : QuotientSpace → QuotientSpace))
      DFunLike.coe_injective
  have h := quotientAction.comap_pCore_of_ker_isPGroup quotientAction_surjective
    (quotientAction_ker.symm ▸ kernel_isTwoGroup)
  rw [BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot] at h
  exact quotientAction_ker.symm.trans h

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
