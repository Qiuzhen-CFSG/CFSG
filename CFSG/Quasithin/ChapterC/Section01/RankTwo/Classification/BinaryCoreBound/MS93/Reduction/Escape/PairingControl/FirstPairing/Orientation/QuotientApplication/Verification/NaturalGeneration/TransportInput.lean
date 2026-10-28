module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source

/-!
# Inputs for transporting the opposite natural plane to the selected seed

The data describe a natural quotient of H, an element in the projection
kernel with a nonzero coordinate fixed by the first marked parabolic, and
a subgroup Z killed by the coordinates. The seed is exactly Z joined with
the first parabolic's normal closure of that element. The untilded local
residuals must cover the actual model parabolics.

There is no natural rank-one factor or local-closure image assertion in
these inputs. Their construction for the selected seed is independent of
the matrix plane calculation and its local-closure transport.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.883.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
open RankOnePairing
variable {G : Type*} [Group G]

/-- Precise natural quotient and seed data, before the opposite closure calculation. -/
structure NaturalSeedData (π : G →* SL) (flag : SL) (i : Bool)
    (H N Z : Subgroup G) (x : G) where
  natural : NaturalFactor π ⊤ H N
  projection_surjective : Function.Surjective π
  residual_image : ∀ j, (localResidual (parabolic π flag j)).map π = modelParabolic flag j
  fixed_le_group : N ≤ H
  z_le_fixed : Z ≤ N
  z_le_kernel : Z ≤ π.ker
  element_mem : x ∈ H
  element_kernel : x ∈ π.ker
  nonzero : natural.coordinates ⟨x, element_mem⟩ ≠ 1
  fixed : ∀ g ∈ modelParabolic flag i,
    (natural.marking g).val.mulVec (natural.coordinates ⟨x, element_mem⟩).toAdd =
      (natural.coordinates ⟨x, element_mem⟩).toAdd

namespace NaturalSeedData
variable {π : G →* SL} {flag : SL} {i : Bool} {H N Z : Subgroup G} {x : G}

/-- The nonzero coordinate of the original selected element. -/
abbrev vector (d : NaturalSeedData π flag i H N Z x) :=
  d.natural.coordinates ⟨x, d.element_mem⟩

/-- The seed includes Z and retains the literal first parabolic closure. -/
def seed (_d : NaturalSeedData π flag i H N Z x) : Subgroup G :=
  Z ⊔ localGenerated (parabolic π flag i) (zpowers x)

end NaturalSeedData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
