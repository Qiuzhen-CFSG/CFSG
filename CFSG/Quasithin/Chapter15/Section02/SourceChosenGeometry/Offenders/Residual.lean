module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Selection
public import Theory.GroupTheory.MaxElementaryResidualDisplacement

/-!
# Residual containment for the original maximum actors

J(T) centralizes V and T normalizes V. Matching maximum elementary actors
modulo O²(H) therefore puts [U_H,A] in the actual embedded O²(H), for every
maximum elementary A in H. The proof transports the intrinsic theorem along
H.subtype, preserving both the orbit span and the residual embedding.

Source: the containment needed in Aschbacher--Smith 15.2.11(2), p.1111.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- The actual orbit span is displaced into the residual by every maximum
elementary subgroup of H, with no chief-action premise. -/
theorem ChosenSmallSource.maximal_span_commutator_le_residual
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hA : A ∈ elementaryAbelianMaxSubgroups H) :
    ⁅conjugateSpan H V,A⁆ ≤ ChosenGeometry.residual H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hVH : V ≤ H := (h.prepared.inside_core H hH).trans (twoCore_le H)
  let S := T.subtype hTH
  let W := V.subgroupOf H
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hTH
  have hW : W.map H.subtype = V := map_subgroupOf_eq_of_le hVH
  have hn : (S : Subgroup H) ≤ normalizer (W : Set H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp
      ((h.maximal.1.2.trans h.prepared.normalized) ht) (v : G)
  have hc : ∀ D ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
      D ≤ centralizer (W : Set H) := by
    intro D hD d hd v hv
    have hDm := (maxFamily_map_injective_iff H.subtype H.subtype_injective S D).mpr hD
    rw [hS] at hDm
    exact Subtype.ext (((le_sSup hDm).trans
      (h.centralizing.trans (centralizer_le h.prepared.le_local)))
        (mem_map_of_mem H.subtype hd) v hv)
  have hAm : A.subgroupOf H ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ _).mp
    simpa only [←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1] using hA
  have hh := map_mono (f := H.subtype)
    (maxElementary_span_commutator_le_pResidual S W (A.subgroupOf H) hn hc hAm)
  rw [map_commutator,map_conjugateSpanBy,hW,←MonoidHom.range_eq_map,
    range_subtype,map_subgroupOf_eq_of_le hA.1,←conjugateSpan_eq] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section02
