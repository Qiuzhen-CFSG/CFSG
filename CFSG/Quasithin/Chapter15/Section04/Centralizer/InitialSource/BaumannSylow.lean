module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.OnePlane
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.CardSixteen
public import Stellmacher.BaumannMap

/-!
# Baumann Sylow from the original small moved module

The one-plane and two-plane B.2.18 arguments give the Sylow assertion of
B.6.10 from the actual module and its conjugation images. The ambient
application uses the subgroup inclusion and the restricted original Sylow
subgroup, preserving both Baumann's subgroup and the embedded two-residual.

Source: Aschbacher--Smith B.6.10 and15.4.11, printed pp.117 and1160.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem sylow_from_small_module
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (s : ℕ) (hs : s = 1 ∨ s = 2)
    (hcard : Nat.card W = 2^(2*s)) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 3^s)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 2^s) :
    Chapter1.IsSylowIn 2 (baumann (R : Subgroup G))
      (pResidual 2 G ⊔ baumann (R : Subgroup G)) := by
  rcases hs with rfl | rfl
  · exact sylow_from_one_plane R W hcard hWR hker hLcard hJcard
  · exact sylow_from_card_sixteen R W hcard hWR hker hLcard hJcard

/-- The actual overgroup application, with no replacement for its quotient
map or its embedded residual. -/
theorem ambient_sylow_from_small_module
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (s : ℕ) (hs : s = 1 ∨ s = 2)
    (hcard : Nat.card W = 2^(2*s))
    (hWT : W ≤ ((T.subtype hTH : Sylow 2 H) : Subgroup H))
    (hker : IsPGroup 2 (centralizer (W : Set H)))
    (hLcard : Nat.card ((pResidual 2 H).map
      (MulAut.conjNormal : H →* MulAut W)) = 3^s)
    (hJcard : Nat.card ((elementaryAbelianMaxJ
      ((T.subtype hTH : Sylow 2 H) : Subgroup H)).map
      (MulAut.conjNormal : H →* MulAut W)) = 2^s) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      ((pResidual 2 H).map H.subtype ⊔ baumann (T : Subgroup G)) := by
  have hi := sylow_from_small_module (T.subtype hTH) W s hs hcard hWT hker hLcard hJcard
  have hb : (baumann ((T.subtype hTH : Sylow 2 H) : Subgroup H)).map H.subtype =
      baumann (T : Subgroup G) := by
    simpa only [baumann,thompsonAlpha,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] using
      baumann_map_injective H.subtype H.subtype_injective
        ((T.subtype hTH : Sylow 2 H) : Subgroup H)
  have h := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hi
  rwa [Subgroup.map_sup,hb] at h

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
