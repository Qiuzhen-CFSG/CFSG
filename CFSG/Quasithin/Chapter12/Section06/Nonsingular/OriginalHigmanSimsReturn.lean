module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsPoint
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.ElementaryAbelian.Join

/-!
# Returning original core involutions to the HS moved subgroup

The original moved subgroup V_v maps to an elementary group of order sixteen
in the literal HS quotient and contains the entire covering kernel. A
square-one element of K_v centralizing V_v cannot enlarge that image: HS has
two-rank four. The full-preimage identity therefore returns the element to
the unchanged V_v. In particular this applies to every square-one element
of K_v in the original full core Q, since Q centralizes V.

This is the return step for the preferred common-residual pair of 12.6.12.
It uses no assumption about the center of that residual and does not replace
the full covering kernel or original core by a quotient image.

Source: Aschbacher–Smith, 12.6.12, pp.825–826, with the intrinsic HS two-rank
bound of G.7.3(2), p.348, and the compatible double-cover projection.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem hs_square_one_centralizer_mem
    (W : Subgroup Sporadic.LeechRelated.HS.Carrier) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 16) (x : Sporadic.LeechRelated.HS.Carrier)
    (hx : x ^ 2 = 1) (hc : x ∈ centralizer (W : Set Sporadic.LeechRelated.HS.Carrier)) :
    x ∈ W := by
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian 2 (W ⊔ zpowers x : Subgroup Sporadic.LeechRelated.HS.Carrier) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hc)
  have hb := (primeRank_le_iff_elementary_card_le Sporadic.LeechRelated.HS.Carrier).mp
    Sporadic.LeechRelated.HS.twoRank_le_four (W ⊔ zpowers x) inferInstance
  have he : W = W ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by
    rw [hW]
    exact hb)
  rw [he]
  exact (show zpowers x ≤ W ⊔ zpowers x from le_sup_right) (mem_zpowers x)

/-- A component involution centralizing the original moved subgroup belongs
to that subgroup, with the full covering kernel retained. -/
theorem SourceHypothesis.nonsingular_hs_involution_centralizer_mem_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (x : G) (hxC : x ∈ Kv (v : G)) (hx2 : x ^ 2 = 1)
    (hc : x ∈ centralizer (Vv L V (v : G) : Set G)) :
    x ∈ Vv L V (v : G) := by
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let y : C := ⟨x,hxC⟩
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.subgroupOf (H.nonsingular_component_rank D v hv).1
  let : IsElementaryAbelian 2 (W.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (W.map f) = 16 := by
    rw [show W.map f = (W.map (QuotientGroup.mk' (center C))).map e.toMonoidHom from
      (map_map _ _ _).symm,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  have hy2 : (f y) ^ 2 = 1 := by
    rw [←map_pow,show y ^ 2 = 1 from Subtype.ext hx2,map_one]
  have hyc : f y ∈ centralizer (W.map f : Set Sporadic.LeechRelated.HS.Carrier) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨w,hw,rfl⟩
    have hcomm : w * y = y * w := Subtype.ext (hc w hw)
    simpa only [map_mul] using congrArg f hcomm
  have hym : f y ∈ W.map f := hs_square_one_centralizer_mem (W.map f) hcard (f y) hy2 hyc
  have hyW : y ∈ W := by
    have he := H.nonsingular_hs_moved_full_preimage D v hv hK e
    exact he.le hym
  exact hyW

/-- The same return applies inside the original full core Q, whose action
centralizes V and hence its original moved subgroup. -/
theorem SourceHypothesis.nonsingular_hs_core_involution_mem_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (x : G) (hxC : x ∈ Kv (v : G)) (hxQ : x ∈ Q T L) (hx2 : x ^ 2 = 1) :
    x ∈ Vv L V (v : G) :=
  H.nonsingular_hs_involution_centralizer_mem_moved D v hv hK e x hxC hx2
    (centralizer_le (Vv_le_V H.chosen.normalizes _) (H.chosen.core_centralizes hxQ))

end CFSG.Quasithin.Chapter12.Section06
