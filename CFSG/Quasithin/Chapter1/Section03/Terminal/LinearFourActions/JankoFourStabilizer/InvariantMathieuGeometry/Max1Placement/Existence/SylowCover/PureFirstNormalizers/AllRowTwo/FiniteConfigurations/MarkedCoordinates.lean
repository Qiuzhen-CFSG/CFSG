module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Data

/-!
# Retaining both points in the simultaneous native marking

The original placement proof already constructs membership of both literal
points. This companion retains those memberships in its public conclusion,
using the same conjugator for X, its entire sixteen-overgroup family, its
canonical join and its full normalizer. These are the point hypotheses needed
by the finite census; mere containment in the intersection would lose them.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.MarkedIntersection
open ElementaryNormalizerCover
open Janko4.GeneratorCertificates
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open IntersectionCertificates
local notation "t₀" => OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.t
attribute [local irreducible] modelGroup matrixA matrixB toMatrix

theorem simultaneous_marked_overgroup_coordinates_with_points
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ g : Model,
      t₀ ∈ X.map (MulAut.conj g).toMonoidHom ∧
      (sourceP : Model) ∈ X.map (MulAut.conj g).toMonoidHom ∧
      X.map (MulAut.conj g).toMonoidHom ≤ markedIntersection ∧
      (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤ markedIntersection ∧
      (∀ Y ∈ sixteenOvergroups X, Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection) ∧
      (∀ u ∈ sixteenHull X, ∃ i : Fin 128, (kernelProduct (coordinate i) : Model) = (MulAut.conj g) u) ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
        normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model) := by
  obtain ⟨k,hplane,_,_⟩ := max4_group_placement X hcard hpure hno
  let g := bridge*k⁻¹
  have hp0 : (SymmetricLinear.NormalEight.element 1 : Model) ∈
      CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.max4Plane := by
    exact ⟨_,⟨(1 : Fin 4),rfl⟩,rfl⟩
  have ht0 : (SymmetricLinear.NormalEight.element 2 : Model) ∈
      CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.max4Plane := by
    exact ⟨_,⟨(2 : Fin 4),rfl⟩,rfl⟩
  have hpoints (Y : Subgroup Model) (hXY : X ≤ Y) :
      t₀ ∈ Y.map (MulAut.conj g).toMonoidHom ∧
        (sourceP : Model) ∈ Y.map (MulAut.conj g).toMonoidHom := by
    constructor
    · refine ⟨(MulAut.conj k) (SymmetricLinear.NormalEight.element 2 : Model),
        hXY (hplane (mem_map_of_mem _ ht0)),?_⟩
      change (bridge*k⁻¹)*(k*_ *k⁻¹)*(bridge*k⁻¹)⁻¹ = t₀
      simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
        inv_mul_cancel,mul_one] using marking.2.1
    · refine ⟨(MulAut.conj k) (SymmetricLinear.NormalEight.element 1 : Model),
        hXY (hplane (mem_map_of_mem _ hp0)),?_⟩
      change (bridge*k⁻¹)*(k*_ *k⁻¹)*(bridge*k⁻¹)⁻¹ = (sourceP : Model)
      simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
        inv_mul_cancel,mul_one] using marking.1
  have hplace (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
      (hXY : X ≤ Y) (hp : ∀ y ∈ Y, y ≠ 1 → IsConj a y)
      (hn : ¬ ∃ c : Model, PureTwoA.NativePair.nativePair.map
        (MulAut.conj c).toMonoidHom ≤ Y) :
      Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    let : IsElementaryAbelian 2 (Y.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
    apply marked_all_row_two_le _ ?_ (no_native_pair_map Y hn g)
      (hpoints Y hXY).1 (hpoints Y hXY).2
    rintro y ⟨z,hz,rfl⟩ hy
    exact (hp z hz (fun he => hy (by simp [he]))).trans (isConj_iff.mpr ⟨g,rfl⟩)
  have hXplace := hplace X le_rfl hpure hno
  have hfamily : ∀ Y ∈ sixteenOvergroups X,
      Y.map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    rintro Y ⟨hXY,_,hE,hp,hn⟩
    let := hE
    exact hplace Y hXY hp hn
  have hhull : (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤ markedIntersection := by
    apply map_le_iff_le_comap.mpr
    exact sup_le (map_le_iff_le_comap.mp hXplace)
      (sSup_le fun Y hY => map_le_iff_le_comap.mp (hfamily Y hY))
  refine ⟨g,(hpoints X le_rfl).1,(hpoints X le_rfl).2,
    hXplace,hhull,hfamily,?_,map_equiv_normalizer_eq _ _⟩
  intro u hu
  exact (mem_markedIntersection_iff _).mp (hhull (mem_map_of_mem _ hu))


end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.MarkedIntersection
