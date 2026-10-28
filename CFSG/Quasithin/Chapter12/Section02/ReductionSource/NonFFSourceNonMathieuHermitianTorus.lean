module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceTorus

/-!
# Odd parabolic tori on the original chosen Hermitian orbit

The full original automizer embeds in the binary Hermitian normalizer via
the chosen module's actual subgroup coordinates. The intertwiner identifies
its literal cyclic fixed spaces, and the embedding preserves actor orders.
Thus an odd actor with fixed rank greater than 3n and the marked parabolic
has order dividing 2^(4n)−1; its fixed rank is divisible by n.

The half-field tensor input constructs those coordinates on the original
component and supplies the same statement for every original actor. This
removes the model geometry callbacks needed in the intermediate case of
8.2.3. Constructing the selected pair and preserved parabolic, excluding
k = 2n, the final torus argument, and the field-four endgame remain with
the original Hermitian exclusion owner.

Source: Aschbacher–Smith 3.2.9(4), H.4.2 and 8.2.3, printed
pp.582–583, 380 and 715–716 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem tensor_coordinates_nonempty
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
  ⟨(exists_component_coordinates (ρ := ρ) (Q := Q) hs B C n hdegree hfield hmodel).choose⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The proved parabolic exponent and coefficient-field degree on the original
chosen-orbit automizer, with the literal cyclic fixed space. -/
theorem sourceOrbit_hermitian_odd_parabolic_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (x : Automizer D.sourceOrbit) (ho : Odd (orderOf x))
    (hlarge : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)))
    (hp : PreservesMaximalParabolic n
      (coordinateHom (automizerRepresentation D.sourceOrbit) n
        (D.hermitianOrbitCoordinates n d) x)) :
    n ∣ Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) ∧
      orderOf x ∣ 2^(4*n)-1 := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  have hc : coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d) x = (j x).val := by
    apply LinearEquiv.ext
    intro w
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  have hf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    have hm := fixedSpace_map_equivariant (automizerRepresentation D.sourceOrbit)
      (overgroupAction n (binaryNormalizer n)) j (D.hermitianOrbitCoordinates n d) he
      (zpowers x)
    rw [MonoidHom.map_zpowers] at hm
    rw [← hm,LinearEquiv.finrank_map_eq]
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,hd⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hoj (hf ▸ hlarge)
  have hoj' : Odd (orderOf (j x).val) := by rwa [Subgroup.orderOf_coe]
  have hb := oddLinearParabolicExponent n (j x).val (j x).property hoj' hl (hc ▸ hp)
  rw [Subgroup.orderOf_coe,orderOf_injective j hj] at hb
  exact ⟨by rwa [hf],hb⟩

/-- The literal half-field tensor constructs its coordinates and supplies the
same bound on every original odd actor with the marked parabolic and large
fixed space. No replacement action or geometric callback is assumed. -/
theorem sourceOrbit_hermitian_tensor_odd_parabolic_order
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    ∃ d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
        (overgroupAction n (binaryImage n)),
      ∀ x : Automizer D.sourceOrbit, Odd (orderOf x) →
        3*n < Module.finrank (ZMod 2)
          (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) →
        PreservesMaximalParabolic n
          (coordinateHom (automizerRepresentation D.sourceOrbit) n
            (D.hermitianOrbitCoordinates n d) x) →
        n ∣ Module.finrank (ZMod 2)
          (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) ∧
          orderOf x ∣ 2^(4*n)-1 := by
  have hd : Nonempty (ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :=
    tensor_coordinates_nonempty (A := D.orbitActor) (U := D.orbitSpace)
      D.orbitRepresentation D.orbitComponent hs B C n hdegree hfield hmodel
  let d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)) := Classical.choice hd
  exact ⟨d,D.sourceOrbit_hermitian_odd_parabolic_order h.toHypothesis1221 n d⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
