module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenCover

/-!
# The actual cubic actor at the terminal comparison

For the original small MS pair, H = K O₂(M) maps onto the even hexacode
group with precisely its original two-core as kernel. The preimage of the
cubic center is exactly the original extension kernel restricted to H.
Thus passing from H to the six-letter even image removes the cubic center,
whereas the retained terminal actor keeps it.

The construction uses the source component in M/O₂(M); no original Sylow
hypothesis or identification of M/O₂(M) with a symmetric group is involved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalActor
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "H" => (K ⊔ Q : Subgroup M)

/-- The source projection keeps the actual cubic central cover. -/
@[expose] def projection : H →* Atlas.Codes.HexEvenAutomorphisms :=
  OriginalSylow.evenCoverProjection h e hz

theorem projection_surjective : Function.Surjective (projection h e hz) :=
  OriginalSylow.evenCoverProjection_surjective h e hz

theorem projection_kernel : (projection h e hz).ker = (Q).subgroupOf H :=
  OriginalSylow.evenCoverProjection_kernel h e hz

theorem projection_kernel_isPGroup : IsPGroup 2 (projection h e hz).ker :=
  OriginalSylow.evenCoverProjection_kernel_isPGroup h e hz

/-- The retained cubic center has the full original E as its preimage. -/
theorem projection_center_preimage :
    (center Atlas.Codes.HexEvenAutomorphisms).comap (projection h e hz) =
      (extensionKernel h).subgroupOf H := by
  let a := OriginalSylow.evenCoverMarking h e hz
  ext x
  change projection h e hz x ∈ center Atlas.Codes.HexEvenAutomorphisms ↔
    (x : M) ∈ extensionKernel h
  rw [extensionKernel_eq_comap_centralizer h e]
  change a (OriginalSylow.evenCoverToComponent x) ∈
      center Atlas.Codes.HexEvenAutomorphisms ↔
    QuotientGroup.mk' Q (x : M) ∈
      centralizer (componentImage L R : Set (M ⧸ Q))
  rw [mem_center_iff]
  constructor
  · intro hx y hy
    have he : (⟨y, hy⟩ : componentImage L R) * OriginalSylow.evenCoverToComponent x =
        OriginalSylow.evenCoverToComponent x * ⟨y, hy⟩ := by
      apply a.injective
      simpa only [map_mul] using hx (a ⟨y, hy⟩)
    simpa only [Subgroup.coe_mul, OriginalSylow.evenCoverToComponent_apply] using
      congrArg (fun z : componentImage L R => (z : M ⧸ Q)) he
  · intro hx y
    obtain ⟨z, rfl⟩ := a.surjective y
    rw [← map_mul, ← map_mul]
    apply congrArg a
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, OriginalSylow.evenCoverToComponent_apply] using
      hx z z.property

/-- The even preimage is KQ; its quotient by Q still contains the cubic center. -/
theorem actor_eq_even_preimage (hk : layerKernel L R = extensionKernel h) :
    H = (alternatingGroup (Fin 6)).comap (CubicAction.projection h e hz hk) :=
  OriginalSylow.evenCoverGroup_eq_even_preimage h e hz hk

include e hz in
/-- The actual terminal source actor, with both kernels identified. -/
theorem exists_projection :
    ∃ q : H →* Atlas.Codes.HexEvenAutomorphisms,
      Function.Surjective q ∧ q.ker = (Q).subgroupOf H ∧
        (center Atlas.Codes.HexEvenAutomorphisms).comap q =
          (extensionKernel h).subgroupOf H :=
  ⟨projection h e hz, projection_surjective h e hz,
    projection_kernel h e hz, projection_center_preimage h e hz⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalActor
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
