module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Offenders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.RankOneOffenders.Section
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.RankOneOffenders.Construction
public import Theory.Representation.SL2NaturalOffenders

/-!
# Maximum elementary images are rank-one Sylow subgroups

Under the explicit kernel equality C_D(V) = O₂(D), the block model supplies
a faithful invariant section of V = Ω₁(Z(O₂(D))) with the natural SL₂ action.
Each nontrivial maximum elementary image is an offender on this section.
The intrinsic natural-module offender theorem places it in the first image
and identifies it with a Sylow two-subgroup.

Restriction of the action-range inclusion then transports the Sylow subgroup
to the literal omega-center automorphism image. The kernel equality remains
an explicit hypothesis for the parent assembly to discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(1),
printed p.86, and the rank-one case of C.2.7, pp.145–146, used in 15.4.20,
p.1164.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
noncomputable section

/-- Restricting the inclusion of the action range identifies the two first images. -/
def faithfulFirstEquiv : faithfulImage b b.first ≃* image b b.first :=
  ((faithfulImage b b.first).equivMapOfInjective (action b).range.subtype
    (action b).range.subtype_injective).trans
    (MulEquiv.subgroupCongr (faithfulImage_map b b.first))

/-- The equivalence preserves the underlying omega-center automorphism. -/
theorem faithfulFirstEquiv_apply (x : faithfulImage b b.first) :
    ((faithfulFirstEquiv b x : image b b.first) : MulAut (omegaModule b)) =
      ((x : ActionGroup b) : MulAut (omegaModule b)) := rfl

/-- Sylow recognition in the faithful action group gives the requested literal
subgroup equality in the omega-center automorphism group. -/
theorem sylow_image_of_faithfulImage {A : Subgroup G}
    (h : ∃ P : Sylow 2 (faithfulImage b b.first),
      (P : Subgroup (faithfulImage b b.first)).map (faithfulImage b b.first).subtype =
        faithfulImage b A) :
    ∃ P : Sylow 2 (image b b.first),
      (P : Subgroup (image b b.first)).map (image b b.first).subtype = image b A := by
  obtain ⟨P, hP⟩ := h
  let f := (faithfulFirstEquiv b).toMonoidHom
  have hf : Function.Surjective f := fun y => (faithfulFirstEquiv b).surjective y
  refine ⟨P.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, map_map]
  change (P : Subgroup (faithfulImage b b.first)).map
    ((action b).range.subtype.comp (faithfulImage b b.first).subtype) = image b A
  rw [← map_map, hP, faithfulImage_map]

/-- Every nontrivial maximum elementary image is a Sylow two-subgroup of the
literal first-block image. The natural section and its faithful action are
constructed from the block model; only the prescribed kernel equality remains
conditional. -/
theorem maximum_image_isSylow (hQ : blockRadicalCore b ≤ contraryCore c)
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    {A : Subgroup G}
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (contraryCore c))
    (hne : image b A ≠ ⊥) :
    ∃ P : Sylow 2 (image b b.first),
      (P : Subgroup (image b b.first)).map (image b b.first).subtype = image b A := by
  obtain ⟨F, hF, hfin, hAlg, hcard, ⟨s⟩⟩ := exists_naturalSection b hker
  have hsize : 2 < Nat.card F := by
    rw [hcard]
    have hfour : 2 ^ 2 ≤ 2 ^ b.n :=
      Nat.pow_le_pow_right (by decide : 0 < 2) b.model.1
    exact lt_of_lt_of_le (by decide) hfour
  apply sylow_image_of_faithfulImage b
  exact Representation.SL2NaturalOffenders.exists_sylow hsize
    (faithfulImage b b.first) s.firstIso s.naturalAction s.naturalAction_injective
    s.naturalAction_first (s.maximum_isOffender hQ hA hne)

end
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
