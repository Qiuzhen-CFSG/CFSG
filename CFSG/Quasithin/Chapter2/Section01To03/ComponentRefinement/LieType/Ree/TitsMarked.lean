module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LocalPair
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders

/-!
# Marked Tits subgroups in a component

An actual equivalence with Parrott's group transports the two certified Atlas
parabolics into L. They generate L, and the first has order 10240, excluding
every χ₀ subgroup. If the marking sends the literal inner projection of z
to the distinguished central involution r5, the first transported parabolic
lies in M because it centralizes z. Adjoining the given Sylow subgroup
preserves this containment, even when that subgroup permutes components.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, and Parrott (1972), §5.
The suitable marking, N_S(L)-invariance, local characteristic two and the
second-parabolic block calculation are still required for the exclusion.
The carrier here is the Tits simple group, not full ²F₄(2).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

open Subgroup ChapterC

variable {G : Type*} [Group G] {L : Subgroup G}

/-- The checked comparison with the Atlas realization of the Tits group. -/
noncomputable def titsAtlasEquiv (e : L ≃* Tits.ParrottGroup) :
    L ≃* Tits.Atlas1600Group := e.trans Tits.parrottFiniteImageEquiv

noncomputable def titsFirst (e : L ≃* Tits.ParrottGroup) : Subgroup L :=
  Tits.ExceptionalParabolics.first.map (titsAtlasEquiv e).symm.toMonoidHom

noncomputable def titsSecond (e : L ≃* Tits.ParrottGroup) : Subgroup L :=
  Tits.ExceptionalParabolics.second.map (titsAtlasEquiv e).symm.toMonoidHom

/-- Both actual parabolics generate the component under any model equivalence. -/
theorem tits_generate (e : L ≃* Tits.ParrottGroup) :
    titsFirst e ⊔ titsSecond e = ⊤ := by
  rw [titsFirst, titsSecond, ← Subgroup.map_sup, Tits.ExceptionalParabolics.generate,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact (titsAtlasEquiv e).symm.surjective

theorem titsFirst_card (e : L ≃* Tits.ParrottGroup) :
    Nat.card (titsFirst e) = 10240 := by
  rw [titsFirst, Subgroup.card_map_of_injective (titsAtlasEquiv e).symm.injective]
  exact Tits.ReeLocalBlockOrders.first_card

/-- This statement concerns every subgroup of the first parabolic, including
all possible relatively subnormal blocks. -/
theorem titsFirst_not_chiZero (e : L ≃* Tits.ParrottGroup)
    (B : Subgroup (titsFirst e)) : ¬ IsChiZeroBlock B := by
  apply not_chiZero_subgroup_of_three_free (B := B)
  rw [titsFirst_card]
  decide

/-- Transport the distinguished central involution together with the parabolic. -/
theorem titsFirst_le_centralizer (e : L ≃* Tits.ParrottGroup) :
    titsFirst e ≤ centralizer {(titsAtlasEquiv e).symm Tits.atlas1600R5} := by
  apply (Subgroup.map_mono Tits.ExceptionalParabolics.first_le_centralizer).trans
  simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
    map_centralizer_le_centralizer_image {Tits.atlas1600R5}
      (titsAtlasEquiv e).symm.toMonoidHom

/-- A marking compatible with the literal inner action puts the first local
overgroup inside M. No normality of L in the Sylow overgroup is assumed. -/
theorem titsFirstOver_le_of_projection {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hproj : IsConjugationProjection L z
      ((titsAtlasEquiv e).symm Tits.atlas1600R5)) :
    (titsFirst e).map L.subtype ⊔ (S : Subgroup H).map H.subtype ≤ M := by
  apply sup_le ?_ h.sylow_le
  apply le_trans ?_
    ((projection_centralizer_le_intersection hproj h.centralizer_le).trans inf_le_right)
  apply le_inf (map_subtype_le _)
  apply (Subgroup.map_mono (titsFirst_le_centralizer e)).trans
  simpa only [Set.image_singleton, Subgroup.coe_subtype] using
    map_centralizer_le_centralizer_image
      {(titsAtlasEquiv e).symm Tits.atlas1600R5} L.subtype

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
