module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverInvolutions

/-!
# Ambient inclusions for the extended graph-field centralizer

The lower calculation takes I as its ambient group. Here I is itself the
source subgroup of G, and both subtype maps are retained. Thus the range is
exactly I ∩ C_G(w). The linear E₉ residual maps into the odd core of this
relative centralizer. This is only one inclusion; the full odd-core and
Sylow-three conclusions await the residual-action calculation.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137. This module makes
no identification with the joint centralizer of V₁ and w.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.OvergroupThreeLocal
open Subgroup Matrix.PSL3Four.ExtendedCentralizer
variable {G : Type*} [Group G] (I : Subgroup G)

/-- Inclusion of the actual relative centralizer into G. -/
@[expose] def centralizerInclusion (w : I) : centralizerIn w →* G :=
  I.subtype.comp (centralizerIn w).subtype

theorem centralizerInclusion_injective (w : I) :
    Function.Injective (centralizerInclusion I w) :=
  I.subtype_injective.comp (centralizerIn w).subtype_injective

theorem centralizerInclusion_range (w : I) :
    (centralizerInclusion I w).range = I ⊓ centralizer ({(w : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.val.property, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.property)
  · rintro ⟨hxI, hxw⟩
    refine ⟨⟨⟨x, hxI⟩, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hxw)

/-- The odd core is computed inside C_I(w) before embedding in G. -/
@[expose] def oddCoreInAmbient (w : I) : Subgroup G :=
  (pPrimeCore 2 (centralizerIn w)).map (centralizerInclusion I w)

/-- The intrinsic linear residual, embedded through both ambient maps. -/
@[expose] def residualInAmbient (L : Subgroup I) (w : I) : Subgroup G :=
  (residualIn (L := L) w).map (centralizerInclusion I w)

variable (L : Subgroup I) [L.Normal]

theorem residualInAmbient_le_oddCore (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃*
      Matrix.PSL3Four.ExtendedCentralizer.ElementaryNine) :
    residualInAmbient I L w ≤ oddCoreInAmbient I w :=
  map_mono (residualIn_le_oddCore w e)

theorem residualInAmbient_card (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃*
      Matrix.PSL3Four.ExtendedCentralizer.ElementaryNine) :
    Nat.card (residualInAmbient I L w) = 9 := by
  rw [residualInAmbient, card_map_of_injective (centralizerInclusion_injective I w)]
  exact residualIn_card w e

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.OvergroupThreeLocal
