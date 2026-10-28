module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.ExceptionalImage
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization

/-!
# The genuine initial-E Baumann Sylow application

The supplied B.2.16 exceptional datum determines the original moved
module and its canonical action. Its full cubic product covers the
global Thompson image together with J(S). Minimal-parabolic generation
then identifies the residual image; the internal module decomposition
gives faithfulness and the exact image orders. The already proved
one-plane and two-plane Baumann arguments therefore apply with every
module premise discharged.

The ambient theorem retains the original subgroup H, restricted Sylow
subgroup and embedded O²(H), and assumes no B.6.10 conclusion.
Source: Aschbacher--Smith B.6.10 and15.4.11, printed pp.117 and1160.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open Chapter1.RadicalNormalizers.ThompsonSource FamilySource.ThompsonFactors
open ChapterB
variable {H : Type*} [Group H] [Finite H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure S)]

theorem exceptional_action_orders (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2)
    (hker : centralizer (closure S : Set H) = pCore 2 H)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤) :
    Nat.card ((pResidual 2 H).map
      (MulAut.conjNormal : H →* MulAut (moduleGroup d))) = 3^d.count ∧
    Nat.card ((elementaryAbelianMaxJ (S : Subgroup H)).map
      (MulAut.conjNormal : H →* MulAut (moduleGroup d))) = 2^d.count := by
  classical
  have hr := residual_star_image d hc hker hunique
  have hR : (pResidual 2 H).map (starMap (closure S)) ≤ thompsonImage := by
    rw [hr]
    exact cubicProduct_le d _
  constructor
  · rw [conjugation_image_card d _ hR,hr]
    have hi : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
        (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa using hc
    simpa only [Finset.card_univ,Fintype.card_fin] using cubicProduct_card d Finset.univ hi
  · rw [conjugation_image_card d _ (map_mono (elementaryAbelianMaxJ_sylow_le_top S))]
    exact sylowImage_card d

/-- B.6.10's needed Sylow conclusion from the original exceptional
decomposition, with the moved-module data entirely constructed. -/
theorem sylow_of_exceptional (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2)
    (hker : centralizer (closure S : Set H) = pCore 2 H)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤) :
    Chapter1.IsSylowIn 2 (baumann (S : Subgroup H))
      (pResidual 2 H ⊔ baumann (S : Subgroup H)) := by
  have ho := exceptional_action_orders d hc hker hunique
  exact sylow_from_small_module S (moduleGroup d) d.count hc
    (moduleGroup_card d hc) (moduleGroup_le_sylow d)
    (moduleGroup_centralizer_two d hc hker hunique) ho.1 ho.2

/-- The literal outside-overgroup application needed by source15.4.11(3).
The centralizer equality and minimal-parabolic hypothesis discharge the
intrinsic kernel and unique-maximal hypotheses. -/
theorem ambient_sylow_of_exceptional
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hP : IsMinimalParabolicOver T M)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))]
    (d : Exceptional (T.subtype hTM)) (hc : d.count = 1 ∨ d.count = 2) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      ((pResidual 2 M).map M.subtype ⊔ baumann (T : Subgroup G)) := by
  have hk := FamilySource.ThompsonSource.star_kernel T M hTM hC
  have hu : Order.HasUniqueMaximalOver ((T.subtype hTM : Sylow 2 M) : Subgroup M) ⊤ :=
    (ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T M hP).1
  have ho := exceptional_action_orders d hc hk hu
  exact ambient_sylow_from_small_module T M hTM (moduleGroup d) d.count hc
    (moduleGroup_card d hc) (moduleGroup_le_sylow d)
    (moduleGroup_centralizer_two d hc hk hu) ho.1 ho.2

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
