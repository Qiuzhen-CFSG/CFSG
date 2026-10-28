module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight.Centralizer
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight.QuotientGeometry

/-!
# The source elementary eight in its ambient local geometry

This assembles the geometric input for the elementary-centralizer extension
in the `|C_R(K)| = 2` branch of Aschbacher–Smith, Proposition 6.2.13,
printed pp.686–688 (PDF pp.703–705). Here `S` denotes the source `Z_S`.
The subgroup is literally `U = ⟨Z_S^H⟩`, formed inside `H = C_G(z)`, and
`P` is a subgroup of `H`. Its normality is in `H`, not in `G`.

The intrinsic orbit argument proves that `U` is elementary of order eight
and contains `Z(P)`. The quaternion factors and the actual `H/P` quotient
then give `|C_H(U)| = 16`. To locate `U`, map it into the ambient group and
restrict it to `M`: its containment in `P ≤ T` puts it in `M`, and its
normality in `H` implies normality in `T`. The branch equality `U ∩ V = Z_S`
gives the order-two quotient image. The compatible `M/V ≃ S₅` carrying
`L/V` to `A₅` then puts `U` in `T ∩ L`.

`NaturalFourOrbit` is the explicit input produced by the preceding G.6.4(2)
invocation after excluding `S₆` and `S₇`; its producer is
`qt-6-02-m22-branch`. These theorems prove the geometric consequence of
that input. They do not prove the preceding branch reduction or an M₂₂
recognition theorem. The final elementary-sixteen and symmetric-four
extension assembly remains with `qt-m22-centralizer-elementary-extension`.
-/

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The source normal closure lies in the actual Sylow-layer intersection,
using the common ambient embeddings and the compatible quotient. -/
public theorem sourceEight_le_sylow_inf_layer
    (H M : Subgroup G) (P S : Subgroup H) [P.Normal]
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P)
    (T : Sylow 2 M) (V L : Subgroup M) [V.Normal]
    (hq : CompatibleSymmetricFiveQuotient V L)
    (hTH : (T : Subgroup M).map M.subtype ≤ H)
    (hPT : P.map H.subtype ≤ (T : Subgroup M).map M.subtype)
    (hbranch : (sourceEight S).map H.subtype ⊓ V.map M.subtype = S.map H.subtype) :
    (sourceEight S).map H.subtype ≤ ((T : Subgroup M) ⊓ L).map M.subtype := by
  let U := (sourceEight S).map H.subtype
  let A := U.subgroupOf M
  have hUT : U ≤ (T : Subgroup M).map M.subtype :=
    (map_mono (sourceEight_le_core P S hSP)).trans hPT
  have hUM : U ≤ M := hUT.trans (map_subtype_le _)
  have hAT : A ≤ T := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hUT hx
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy
  have hHU : H ≤ normalizer (U : Set G) := by
    have hn := (sourceEight S).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hTn : (T : Subgroup M) ≤ normalizer (A : Set M) := by
    change (T : Subgroup M) ≤ normalizer (U.subgroupOf M)
    rw [← subgroupOf_normalizer_eq hUM]
    intro x hx
    exact hHU (hTH ⟨x, hx, rfl⟩)
  let : (A.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hAT).mpr hTn
  have hAc : Nat.card A = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv,
      card_map_of_injective H.subtype_injective]
    exact sourceEight_card h ha hZS
  have hi : (A ⊓ V).map M.subtype = S.map H.subtype := by
    rw [map_inf _ _ M.subtype M.subtype_injective, map_subgroupOf_eq_of_le hUM]
    exact hbranch
  have hAV : Nat.card (A ⊓ V : Subgroup M) = 4 := by
    rw [← card_map_of_injective M.subtype_injective, hi,
      card_map_of_injective H.subtype_injective, hS]
  have hAL : A ≤ L := eight_le_layer_of_compatible_quotient V L hq T A hAT hAc hAV
  change U ≤ _
  rw [← map_subgroupOf_eq_of_le hUM]
  exact map_mono (le_inf hAT hAL)

/-- All geometric inputs for the centralizer extension, with the original
branch intersection retained. The elementary and centralizer conclusions
are derived, while the earlier natural quotient action is explicit. -/
public theorem sourceEight_geometry
    (H M : Subgroup G) (P S : Subgroup H) [P.Normal]
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P)
    (T : Sylow 2 M) (V L : Subgroup M) [V.Normal]
    (hq : CompatibleSymmetricFiveQuotient V L)
    (hTH : (T : Subgroup M).map M.subtype ≤ H)
    (hPT : P.map H.subtype ≤ (T : Subgroup M).map M.subtype)
    (hbranch : (sourceEight S).map H.subtype ⊓ V.map M.subtype = S.map H.subtype) :
    (sourceEight S).Normal ∧ IsElementaryAbelian 2 (sourceEight S) ∧
      Nat.card (sourceEight S) = 8 ∧ coreCenter P ≤ sourceEight S ∧
      Nat.card (centralizer (sourceEight S : Set H)) = 16 ∧
      (sourceEight S).map H.subtype ≤ ((T : Subgroup M) ⊓ L).map M.subtype ∧
      (sourceEight S).map H.subtype ⊓ V.map M.subtype = S.map H.subtype ∧
      Nat.card ((sourceEight S).map H.subtype ⊓ V.map M.subtype : Subgroup G) = 4 := by
  refine ⟨inferInstance, sourceEight_elementary h ha hS, sourceEight_card h ha hZS,
    hZS.trans (sourceEight_contains S), sourceEight_centralizer_card h ha hS hZS hSP,
    sourceEight_le_sylow_inf_layer H M P S h ha hS hZS hSP T V L hq hTH hPT hbranch,
    hbranch, ?_⟩
  rw [hbranch, card_map_of_injective H.subtype_injective, hS]
end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
