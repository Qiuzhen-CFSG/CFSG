module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.Source
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.OvergroupApplication
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.LocalOrder
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives

/-!
# The source three-local theorem and its graph applications

From the explicit `CentralizerCalculation`, the checked proofs identify
Z(C_G(X)) with the actual X, show that C_G(X) is quasisimple with central
quotient A₆, and identify N_G(X)/X with genuine PGL₂(9). They retain the
inverting involution and complement, the ambient image of E(N_G(X)), and
the order 2160. An order-eight element, not a semidihedral assertion,
distinguishes the required exceptional A₆ extension from the natural S₆.

`SevenRatio` separately proves the preliminary seven-local ratio used in
the centralizer recognition. The result does not use printed 47.4.

`EarlierConclusions.sourceConclusion` assembles all four clauses of 47.3
from the exact 47.1–47.2 inputs for a finite simple ambient group. The
centralizer-recognition construction supplies the perfect A₆ cover and
both normalizer actors. The second-normalizer and projective-lifting
arguments then supply both element classes and the marked extraspecial
Sylow subgroup, including its eight-complement and weak closure.

`OvergroupApplication` identifies the image of the centralizer under the
literal projective quotient map, discharging the vertex-overgroup consumer.
`LocalOrder` also proves |N_H(X)| = 48. Together with |N_G(X)| = 2160
and the Sylow structure, this discharges every three-local premise in the
47.5 representative construction. The resulting four-suborbit theorem has
only the same earlier 47.1–47.2 inputs. Their producers remain
`qt-i47-j2-source-involutions` and `qt-i47-j2-five-local-calculation`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3 and 47.5, pp.261–263.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The conclusions of 47.3, retaining the actual relative quotients,
embedded layer, inverting complement, and intrinsic Sylow action.
This is an output contract, constructed from earlier conclusions below. -/
structure SourceConclusion (D : Seed G) : Prop where
  centralizer_quasisimple : IsQuasisimple (C D)
  centralizer_center : center (C D) = XC D
  centralizer_quotient : Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6))
  center_quotient : Nonempty ((C D ⧸ center (C D)) ≃* alternatingGroup (Fin 6))
  centralizer_card : Nat.card (C D) = 1080
  normalizer_quotient : Nonempty ((M D ⧸ XM D) ≃*
    GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
  projective_image : ∀ e : (M D ⧸ XM D) ≃*
      GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F,
    (CM D).map (Overgroups.vertexModelMap D e) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := Atlas.Comparisons.Exceptional.Nine.F)).range
  normalizer_split : ∃ t : M D, orderOf t = 2 ∧
    (∀ x : D.X, (t : G) * x * (t : G)⁻¹ = (x : G)⁻¹) ∧
    (CM D).IsComplement' (zpowers t)
  layer_image : (componentLayer (M D)).map (M D).subtype = C D
  normalizer_card : Nat.card (M D) = 2160
  local_normalizer_card : Nat.card (SL23Local.localNormalizer D) = 48
  fusion : ThreeFusion D
  sylow : ∀ P : Sylow 3 G, Nonempty (SylowThreeStructure D P)

/-- The subgroup orbit in clause (1) is precisely the source vertex set. -/
theorem threeA_subgroup_orbit {x : G} (hx : ThreeA D x) :
    MulAction.orbit (ConjAct G) (zpowers x) = MulAction.orbit (ConjAct G) D.X :=
  MulAction.orbit_eq_iff.mpr hx.2

/-- Aschbacher 47.3, with the centralizer and Sylow-fusion calculations
discharged. Only the exact earlier 47.1–47.2 conclusions remain. -/
theorem EarlierConclusions.sourceConclusion [IsSimpleGroup G] (E : EarlierConclusions D) :
    SourceConclusion D := by
  obtain ⟨H⟩ := E.centralizerCalculation
  obtain ⟨hfusion, hsylow⟩ :=
    threeFusion_and_sylowStructure H E.card E.geometry E.five
  exact {
    centralizer_quasisimple := H.quasisimple
    centralizer_center := H.center_eq
    centralizer_quotient := H.alternatingQuotient
    center_quotient := ⟨H.centerQuotientEquiv⟩
    centralizer_card := H.centralizer_card
    normalizer_quotient := ⟨H.normalizerQuotientEquiv⟩
    projective_image := H.projective_centralizer_image
    normalizer_split := ⟨H.inverter, H.inverter_order, H.inverts_X, H.split⟩
    layer_image := H.layer_image
    normalizer_card := H.normalizer_card
    local_normalizer_card := local_normalizer_card D
    fusion := hfusion
    sylow := hsylow }

/-- The full source family with its three earlier inputs displayed separately. -/
theorem sourceConclusion_of_source [IsSimpleGroup G] (hG : Nat.card G = 604800)
    (geometry : InvolutionGeometry.SelectedGeometry D)
    (five : FiveLocal.SourceConclusion D geometry.t) : SourceConclusion D :=
  (show EarlierConclusions D from ⟨hG, geometry, five⟩).sourceConclusion

/-- The normalizer calculation supplies the 280 vertices used by 47.5. -/
theorem vertex_card_of_calculation (H : CentralizerCalculation D)
    (hG : Nat.card G = 604800) : Nat.card D.Vertex = 280 :=
  vertex_card_of_source_orders D hG H.normalizer_card

/-- Application to the actual source suborbit construction: the 2160 premise
is now discharged by the centralizer calculation. -/
theorem fourSuborbits_of_calculation (H : CentralizerCalculation D)
    (hG : Nat.card G = 604800) (R : ThreePairRepresentatives D) : FourSuborbits D :=
  R.fourSuborbits hG H.normalizer_card

/-- The 47.3 calculation supplies the 280 vertices without a local-order premise. -/
theorem EarlierConclusions.vertex_card [IsSimpleGroup G] (E : EarlierConclusions D) :
    Nat.card D.Vertex = 280 :=
  vertex_card_of_source_orders D E.card E.sourceConclusion.normalizer_card

/-- Application to the actual 47.5 construction: its Sylow structure and both
normalizer orders are now supplied by 47.3. No pair representative or
four-suborbit conclusion is assumed. -/
theorem EarlierConclusions.fourSuborbits [IsSimpleGroup G] (E : EarlierConclusions D) :
    FourSuborbits D := by
  have h := E.sourceConclusion
  exact Representatives.fourSuborbits_of_earlier_source E.geometry E.five.root
    E.five.twoCentral h.sylow h.normalizer_card h.local_normalizer_card E.card

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
