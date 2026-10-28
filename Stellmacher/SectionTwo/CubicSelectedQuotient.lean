module
public import Theory.GroupTheory.PResidual.CubicImageFrattini
public import Stellmacher.SectionTwo.BaumannOmegaSelectedModule
public import Stellmacher.SL2DerivedCard

/-!
# The selected Baumann coordinate before Frattini reduction

The selected coordinate has a cubic residual image through the original
quotient. When that quotient has two-group kernel, the preceding residual
calculation removes the Frattini subgroup from K/O₂(K). Thus the selected
coordinate itself has the actual SL₂(2) core quotient.

The second theorem uses the exact double subtype map in the native
`baumann_omega_selected_module` conclusion. Source: Stellmacher (2.4),
applied in Aschbacher--Smith C.1.26, printed p.132.
-/

public section
open Subgroup Theory.GroupTheory
namespace Stellmacher

/-- The native finite two-residual is the literal prime residual. -/
theorem twoResidualSubgroup_eq_pResidual
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    twoResidualSubgroup K = pResidual 2 K := by
  unfold twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hn,n,hc⟩
    let : N.Normal := hn
    exact ⟨hn,IsPGroup.of_card hc⟩
  · rintro ⟨hn,hp⟩
    exact ⟨hn,hp.exists_card_eq⟩

namespace SectionTwo
variable {G X : Type*} [Group G] [Group X] [Finite G]

/-- The original cubic residual image removes the selected coordinate's
Frattini layer, without changing its two-core quotient. -/
theorem core_isSL2Two_of_cubic_image
    (q : G →* X) (hk : IsPGroup 2 q.ker)
    (hr : Nat.card ((pResidual 2 G).map q) = 3)
    (hf : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    IsSL2Two (G ⧸ pCore 2 G) := by
  have hbot := frattini_pCoreQuotient_eq_bot_of_cubic_image q hk hr
    (SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hf)
  obtain ⟨e⟩ := hf
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hbot).symm.trans e)⟩

/-- Application to the literal residual image of the selected coordinate. -/
theorem selected_core_isSL2Two [Finite X]
    (q : G →* X) (hk : IsPGroup 2 q.ker)
    (E : Subgroup X) (D : Subgroup E) (hD : IsSL2Two D)
    (K : Subgroup G)
    (hr : (twoResidualAmbient K).map q =
      ((commutator D).map D.subtype).map E.subtype)
    (hf : IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K))) :
    IsSL2Two (K ⧸ pCore 2 K) := by
  apply core_isSL2Two_of_cubic_image (q.comp K.subtype)
  · exact hk.comap_subtype
  · rw [←map_map, ←twoResidualSubgroup_eq_pResidual K]
    change Nat.card ((twoResidualAmbient K).map q) = 3
    rw [hr,card_map_of_injective E.subtype_injective,
      card_map_of_injective D.subtype_injective]
    exact isSL2Two_commutator_card hD
  · exact hf
end SectionTwo
end Stellmacher
