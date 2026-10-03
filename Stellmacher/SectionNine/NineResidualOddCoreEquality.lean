module

public import Stellmacher.SectionNine.NineResidualImageOddCore
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Identifying the local residual image with the odd core

A surjective homomorphism from a genuine Section Nine vertex stabilizer
that kills its two-core maps the geometric two-residual onto the entire
odd core of the target. The established local residual-image theorem,
using (3.3), supplies the containment in the odd core. Surjective residual
functoriality identifies that image with the target's two-residual. The
odd core has trivial image in its two-group quotient, proving equality.

This identifies the geometric residual in the literal terminal action
used in Stellmacher (9.10)(3), printed p.57 of
`refs/files/stellmacher-n-group.pdf`. It leaves the separate question of
which canonical (1.7) factors generate that odd core to the geometric
argument; no transvection or factor-generation hypothesis is needed here.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open BenderSuzuki.External

universe u

public theorem nine_local_residual_image_eq_oddCore
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (action : GAt ctx.Γ vertex →* X)
    (hsurj : Function.Surjective action) (hkernel : pCore 2 (GAt ctx.Γ vertex) ≤ action.ker) :
    ((EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex)).map action =
      SectionOne.oddCore X := by
  apply le_antisymm
  · exact nine_local_residual_image_le_oddCore ctx vertex neighbor hadj action hsurj hkernel
  have hnative : (EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex) =
      twoResidualSubgroup (GAt ctx.Γ vertex) := by
    rw [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective (GAt ctx.Γ vertex).subtype_injective _
  rw [hnative, SectionThree.twoResidualSubgroup_eq_hktPResidual',
    hktPResidual_map_of_surjective' action hsurj]
  let R := hktPResidual 2 X
  let _ : R.Normal := hktPResidual_normal
  let quotient := QuotientGroup.mk' R
  have htwo : IsPGroup 2 (X ⧸ R) := hktPResidual_quotient_isPGroup
  have hmap : (SectionOne.oddCore X).map quotient = ⊥ := by
    have himage := htwo.to_subgroup ((SectionOne.oddCore X).map quotient)
    have hcop : Nat.Coprime 2 (Nat.card ((SectionOne.oddCore X).map quotient)) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ quotient) pPrimeCore_coprime_card
    rcases himage.card_eq_or_dvd with hcard | hdiv
    · exact Subgroup.eq_bot_of_card_eq _ hcard
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) hdiv)
  have hle := Subgroup.map_le_iff_le_comap.mp hmap.le
  simpa only [MonoidHom.comap_bot, quotient, QuotientGroup.ker_mk'] using hle

end Stellmacher.SectionNine
