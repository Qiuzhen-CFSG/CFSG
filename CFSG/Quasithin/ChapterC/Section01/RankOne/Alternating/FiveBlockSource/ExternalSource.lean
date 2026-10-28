module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.SylowMarking
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalPair
/-!
# The C.1.23 S₅ branch with the original external two-group

Transport the single preselected pair from Baum(T) to the actual Baumann
Sylow of H, apply the proved covered-natural source conclusion, and map
back. The result uses the original C₁(T), C₂(T), ambient J(T), and moved
module support. The hypothesis Baum(T)≤R≤T is retained; T need not be a
subgroup of H. Neither block structure nor a splitting of the module cover
is an input.

The genuine preceding marked S₅ quotient is supplied by the B.5.1/B.6.9
source action producer; the universal pair is the earlier C.1.18 theorem.
Source: C.1.21–23, printed pp.127–130.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

/-- C.1.23's covered S₅ branch on the actual external two-group and the
same preselected canonical pair, including support and Thompson generation. -/
theorem external_source_conclusion
    (T H : Subgroup G) (R : Sylow 2 H)
    (hBR : baumann T ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ T)
    (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann T)) (hD : D.Universal.{u,u}) :
    firstAmbient T D ≤ (center H).map H.subtype ∨
      ((secondAmbient T D).subgroupOf H).Normal ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L.map H.subtype = ⁅L.map H.subtype,elementaryAbelianMaxJ T⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) = ⁅U.map H.subtype,L.map H.subtype⁆ ∧
        (blockU L).map (H.subtype.comp L.subtype) ≤ U.map H.subtype) := by
  obtain ⟨E,hE,hfirst,hsecond,hC,hCE⟩ := external_pair_transport T H R hBR hRT D hD
  have hCH : firstAmbient T D ≤ H :=
    (firstAmbient_le_omegaCenter T D).trans ((omegaCenter_le_baumann T).trans
      (hBR.trans (map_subtype_le _)))
  have hh := source_conclusion R hfit L hcomp hprod eL U q hq hk hL p hp he hfix hJ
    E hE ((firstAmbient T D).subgroupOf H) hC hCE
  rcases hh with hc | hn | ⟨hb,ha,hcomm,hs,hU⟩
  · left
    exact (map_subgroupOf_eq_of_le hCH).symm ▸ map_mono hc
  · right; left
    have heq : (secondAmbient T D).subgroupOf H = E.second.map (baumann (R : Subgroup H)).subtype := by
      rw [←hsecond,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective]
    exact heq.symm ▸ hn
  · right; right
    have hJmap : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype = elementaryAbelianMaxJ T := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      exact elementaryAbelianMaxJ_eq_of_intermediate T _
        ((elementaryAbelianMaxJ_le_baumann T).trans hBR) hRT
    refine ⟨hb,ha,?_,?_,?_⟩
    · have hm := congrArg (map H.subtype) hcomm
      rwa [map_commutator,hJmap] at hm
    · rw [←map_map,hs,map_commutator]
    · rw [←map_map]
      exact map_mono hU
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
