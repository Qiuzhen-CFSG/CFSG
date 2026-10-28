module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.SpanPairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules

/-!
# The line-preimage estimate on the literal source layer quotient

Apply the midpoint-span pairing estimate to LayerModule.spanQuotient, using
its actual projection and the supplied dual coordinates. The subgroup in the
conclusion is the preimage under the original LayerModule projection; its
kernel remains Z_alpha. This application neither chooses another quotient
nor identifies that kernel with U_alpha.

Source: original MS93 (1993), (4.6.12), pp.910--912; the remaining geometric
rank-one displacement and fixed-kernel obligations stay with their owner.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.SpanPairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) {geometry : Geometry R}
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)

include radius hb in
/-- The small-commutator bound on the literal line preimage of the source layer module. -/
theorem layer_line_preimage_commutator_card
    (d : LayerModule source (orbitSpan s.middle))
    (e : d.Space ≃ₗ[ZMod 2] Linear.W)
    (he : ∀ g v, e (d.representation g v) =
      Linear.dual (common.natural.marking g) (e v))
    (w : Multiplicative d.Space) (hw : w ≠ 1) :
    Nat.card (⁅((zpowers w).comap d.projection).map (orbitSpan s.middle).subtype,
      Q R (alpha R)⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  obtain ⟨x, hx⟩ := d.onto w
  let q := d.spanQuotient common e he
  have hxq : q.quotient x ≠ 1 := by
    intro h
    have hk : x ∈ q.quotient.ker := h
    rw [q.kernel, ← d.kernel] at hk
    exact hw (hx.symm.trans hk)
  have hpre : ((zpowers w).comap d.projection).map (orbitSpan s.middle).subtype =
      linePreimage source common s q x := by
    rw [← hx, ← MonoidHom.map_zpowers d.projection, comap_map_eq, d.kernel,
      Subgroup.map_sup, MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le (Z_le_orbitSpan_of_distance_two s.middle s.first_distance),
      linePreimage_eq]
    exact sup_comm _ _
  rw [hpre]
  exact linePreimage_commutator_card source common radius hb s q x hxq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.SpanPairing
