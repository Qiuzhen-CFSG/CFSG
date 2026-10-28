module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.TwoPlanes
public import Theory.GroupTheory.SolvableOuterQuotient
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# The two-plane action from the actual conjugation images

The order-nine residual image in Aut(E₁₆) has the previously proved
orthogonal normalizer coordinates. Normality of the residual puts every
original conjugation in that normalizer. These coordinates preserve all
image orders. The Thompson subgroup preserves the two planes by the
maximum-elementary replacement argument, so the actual image orders
discharge the two-plane B.2.18 application.

Source: Aschbacher--Smith B.6.10, used in15.4.11, printed pp.117 and1160.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open FamilySource.ModuleStructure.BinaryNormalizer
open FamilySource.ModuleStructure.BaumannPair
open LocalSetup.SourceWitnesses.MarkedProduct ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The chart is constructed from the original action, rather than given
as an independent representation-recognition premise. -/
theorem orthogonal_action_of_residual_card_nine
    (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 16)
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 9) :
    ∃ d : Action W,
      (pResidual 2 G).map d.actor = rotations ∧
      ∀ A : Subgroup G, Nat.card (A.map d.actor) =
        Nat.card (A.map (MulAut.conjNormal : G →* MulAut W)) := by
  let ρ := (MulAut.conjNormal : G →* MulAut W)
  let C := (pResidual 2 G).map ρ
  have hn : ρ.range ≤ normalizer (C : Set (MulAut W)) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map] using
      (pResidual 2 G).le_normalizer_map ρ
  let β := ρ.codRestrict (normalizer (C : Set (MulAut W)))
    (fun g => hn ⟨g,rfl⟩)
  obtain ⟨c,e,hc,hce⟩ := double_normalizer_coordinates hcard C hLcard
  let γ := e.toMonoidHom.comp β
  have he : vectorAction.comp γ = (MulAut.congr c).toMonoidHom.comp ρ := by
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro v
    have hh := hce (β g) (c.symm v)
    rw [c.apply_symm_apply] at hh
    exact hh.symm
  let d : Action W :=
    { coordinates := c
      actor := γ
      intertwines := by
        intro g w
        have hh := congrArg c.symm (hce (β g) w)
        rw [c.symm_apply_apply] at hh
        exact (congrArg Subtype.val hh).symm }
  refine ⟨d,?_,?_⟩
  · apply map_injective vectorAction_injective
    change ((pResidual 2 G).map γ).map vectorAction = rotations.map vectorAction
    rw [map_map,he,←map_map]
    change C.map (MulAut.congr c).toMonoidHom = rotations.map vectorAction
    rw [hc]
    exact MonoidHom.map_range vectorAction rotationHom |>.symm
  · intro A
    calc
      Nat.card (A.map d.actor) = Nat.card ((A.map γ).map vectorAction) :=
        (card_map_of_injective vectorAction_injective).symm
      _ = Nat.card ((A.map ρ).map (MulAut.congr c).toMonoidHom) := by
        rw [map_map,he,←map_map]
      _ = Nat.card (A.map ρ) := card_map_of_injective (MulAut.congr c).injective

/-- Only the actual normal module and its conjugation-image orders are
needed for the two-plane Sylow conclusion. -/
theorem sylow_from_card_sixteen
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 16) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 9)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 4) :
    Chapter1.IsSylowIn 2 (baumann (R : Subgroup G))
      (pResidual 2 G ⊔ baumann (R : Subgroup G)) := by
  obtain ⟨d,hL,hcards⟩ := orthogonal_action_of_residual_card_nine W hcard hLcard
  have hk : IsPGroup 2 d.actor.ker := (Action.kernel d).symm ▸ hker
  have hJb : (elementaryAbelianMaxJ (R : Subgroup G)).map d.actor ≤ base := by
    rintro _ ⟨j,hj,rfl⟩
    exact d.thompson_base (elementaryAbelianMaxJ_sylow_le_top R hj)
  exact sylow_from_two_planes R W d hWR hk hL hJb
    ((hcards _).trans hJcard)

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
