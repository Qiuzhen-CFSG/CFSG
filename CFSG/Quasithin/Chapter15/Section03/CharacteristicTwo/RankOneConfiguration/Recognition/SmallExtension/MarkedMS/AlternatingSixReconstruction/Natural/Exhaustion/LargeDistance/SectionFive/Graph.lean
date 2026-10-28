module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Cover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Frattini

/-!
# The natural central quotient on the actual graph moving layer

The earlier central-layer identification transports the whole cover to the
literal subgroup U at the base vertex. Its projection remains surjective,
intertwines actual conjugation, and has kernel the embedded ambient center.
Both possible moved orders, sixteen and thirty-two, are retained.

This is the input quotient U/(U ∩ Z(Gα)) in MS93 (5.0), printed p.912.
The earlier central-layer identification is an explicit independent premise.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
  (hc : DistanceTwo.CentralLayer d)

/-- The inverse of the original graph inclusion on the entire moved cover. -/
def graphMovedEquiv : U d.radical (alpha d.radical) ≃* replacementMoved d :=
  (MulEquiv.subgroupCongr hc.U_eq_moved).trans
    ((replacementMoved d).equivMapOfInjective (embedM d.radical)
      (embedM_injective d.radical)).symm

omit [Finite G] in
theorem graphMovedEquiv_val (v : U d.radical (alpha d.radical)) :
    embedM d.radical (graphMovedEquiv hc v) = v := by
  have he := ((replacementMoved d).equivMapOfInjective (embedM d.radical)
    (embedM_injective d.radical)).apply_symm_apply
      ((MulEquiv.subgroupCongr hc.U_eq_moved) v)
  exact congrArg Subtype.val he

/-- The graph projection is the original cover map through its literal inclusion. -/
def graphCoverProjection : U d.radical (alpha d.radical) →*
    Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (coverProjection h e hz hn d).comp (graphMovedEquiv hc).toMonoidHom

theorem graphCoverProjection_surjective :
    Function.Surjective (graphCoverProjection (h := h) (e := e) (hz := hz) (hn := hn) hc) :=
  (coverProjection_surjective h e hz hn d).comp (graphMovedEquiv hc).surjective

local notation "π" => graphCoverProjection (h := h) (e := e) (hz := hz) (hn := hn) hc

theorem graphCoverProjection_conjugate (g : d.overgroup)
    (v w : U d.radical (alpha d.radical))
    (hw : (w : FreeAmalgam d.radical) =
      embedM d.radical g * v * (embedM d.radical g)⁻¹) :
    (π w).toAdd = BinaryPermutation.naturalRepresentation (Fin 6) (s.projection g)
      (π v).toAdd := by
  apply s.cover_conjugate g (graphMovedEquiv hc v) (graphMovedEquiv hc w)
  apply embedM_injective d.radical
  rw [map_mul, map_mul, map_inv, graphMovedEquiv_val, graphMovedEquiv_val]
  exact hw

include s hc in
theorem graphCoverProjection_kernel :
    (π).ker = ((center d.overgroup).map (embedM d.radical)).comap
      (U d.radical (alpha d.radical)).subtype := by
  ext v
  change graphMovedEquiv hc v ∈ (coverProjection h e hz hn d).ker ↔ _
  rw [coverProjection_kernel_center s]
  constructor
  · intro hv
    exact ⟨graphMovedEquiv hc v, hv, graphMovedEquiv_val hc v⟩
  · rintro ⟨x, hx, he⟩
    have hv : (graphMovedEquiv hc v : d.overgroup) = x :=
      embedM_injective d.radical ((graphMovedEquiv_val hc v).trans he.symm)
    change (graphMovedEquiv hc v : d.overgroup) ∈ center d.overgroup
    rwa [hv]

include s hc in
/-- The graph layer retains both source orders, with no order-sixteen specialization. -/
theorem graph_U_card :
    Nat.card (U d.radical (alpha d.radical)) = 16 ∨
      Nat.card (U d.radical (alpha d.radical)) = 32 := by
  rw [Nat.card_congr (graphMovedEquiv hc).toEquiv]
  exact moved_card s

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
