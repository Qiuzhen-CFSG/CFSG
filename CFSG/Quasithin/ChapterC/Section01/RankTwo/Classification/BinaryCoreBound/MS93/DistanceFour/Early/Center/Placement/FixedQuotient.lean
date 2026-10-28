module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Calculation

/-!
# The selected edge's fixed quotient

The selected noncentral seed gives the source cover Z_a ≤ Vcirc_d Z_d.
The full relative normalizer preserves the incident edge radius and its
nonzero image in the marked natural factor. The finite natural-section
calculation therefore identifies the fixed preimage on the actual V_d/Z_d
as (V_b ∩ Vcirc_d) B_d. All calculation premises are discharged in the
finite stabilizer of d; the free amalgam is not assumed finite.

Both conclusions need only the selected seed and the earlier common and
edge facts. The initial facts, failure of B_a ≤ Z(V_a), and global
noncentrality used to select that seed are not needed again here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.7), printed p.904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The incident kernel's literal fixed preimage, with the finite natural
calculation and every source-specific premise discharged. -/
theorem seed_fixed_quotient (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    radiusFixed geometry d (Q R b) =
      (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d) := by
  let := finite_stabilizer R d
  exact seed_fixed_quotient_of_calculation common hb edge a b d ha hab hdb hseed
    (naturalFixedCalculation (stabilizer R d))

/-- The cover and fixed-quotient calculation used in MS93 (4.6.7).
The parent edge-placement argument consumes the second conclusion. -/
theorem seed_Z_cover_and_fixed_quotient (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    Z R a ≤ Vcirc R d ⊔ Z R d ∧
      radiusFixed geometry d (Q R b) =
        (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d) :=
  ⟨seed_Z_le_moving_sup_Z common hb edge a b d ha hab hdb hseed,
    seed_fixed_quotient common hb edge a b d ha hab hdb hseed⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
