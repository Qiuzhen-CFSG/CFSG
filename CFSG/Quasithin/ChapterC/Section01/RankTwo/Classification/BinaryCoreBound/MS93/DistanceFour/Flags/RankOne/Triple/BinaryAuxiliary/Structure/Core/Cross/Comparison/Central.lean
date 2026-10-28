module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Central.Intersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Central.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Central.Placement

/-!
# Central-layer containment at every escaping midpoint flag

The original Z_alpha lies in the common first layer V_beta. The marked
natural factors force that layer to meet the transported moving plane only
in U_lambda. Thus the earlier placement of Z_alpha in the moving plane
implies Z_alpha <= U_lambda, for the same arbitrary escaping flag.

The placement theorem supplies this premise at every flag whose transported
core is escaped by X_delta0. The final theorem therefore proves the
containment with no additional placement or index hypothesis. The separate
conditional assemblies retain the moving-plane and reverse-index interfaces.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, paragraph beginning “Hence q = 2”.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Placing the original center in the moving summand suffices for its
containment in the second layer. The actual marked factors and their
first-layer intersection supply the source's D > U deduction. -/
theorem middle_center_le_second_of_moving_containment
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hplacement : Z R (alpha R) ≤
      (⁅Y source i e,localFlagActor source (!i) e⁆ ⊔ secondFlagLayer source i e).map
        t.conjugation.toMonoidHom) :
    Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  have hQcross : ¬ Q R (beta R) ≤ localFlagKernel source (!i) e := by
    intro h
    apply hcross
    have hh := map_mono (f := t.conjugation.toMonoidHom) h
    rw [t.map_Q_beta] at hh
    exact (X_le_second source geometry common.large_distance i p.delta0).trans
      ((secondFlagLayer_le_radius source i p.delta0).trans
        ((V_le_Q geometry common.large_distance _ rfl).trans
          ((Q_le_adjacent_h R rfl (base_adjacent R)).trans hh)))
  obtain ⟨me⟩ : Nonempty (MovingFactor source i e) := by
    simpa only [inv_mul_cancel_right] using
      movingFactor_conjugate source geometry common.large_distance i
        (e*p.delta0⁻¹) p.delta0 moving
  obtain ⟨xe⟩ : Nonempty (XFactor source i e) := by
    simpa only [inv_mul_cancel_right] using
      XFactor_conjugate source geometry common.large_distance i
        (e*p.delta0⁻¹) p.delta0 x
  have hi := map_mono (f := t.conjugation.toMonoidHom)
    (first_inf_moving_le_second_of_core_crossing source geometry common early
      i hkernel natural e he me xe hQcross)
  rw [map_inf _ _ _ t.conjugation.injective, t.map_V_beta] at hi
  exact (le_inf Z_le_edgeRadius hplacement).trans hi

/-- Central-layer containment at the specified escaping flag, conditional only
on the earlier reverse index comparison at that same transported flag.
The universal reverse comparison remains an upstream obligation. -/
theorem middle_center_le_second_of_reverse_index
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hreverse : (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
      (Z R p.middle).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆) :
    Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  exact middle_center_le_second_of_moving_containment source geometry common early i hkernel
    natural p t moving x e he hcross
    (middle_center_le_moving_of_reverse_index source geometry common early i hkernel
      p t moving e he hcross hreverse)

/-- At every incident midpoint flag whose transported core is escaped by
X_delta0, the original center lies in the transported second layer.
The earlier center placement and the first/moving intersection discharge
all intermediate premises, with the supplied flag and transporter fixed. -/
theorem middle_center_le_second_of_X_crossing
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom) :
    Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  exact middle_center_le_second_of_moving_containment source geometry common early i hkernel
    natural p t moving x e he hcross
    (middle_center_le_moving_of_X_crossing source geometry common hb early i hkernel
      natural p t moving x e he hcross)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
