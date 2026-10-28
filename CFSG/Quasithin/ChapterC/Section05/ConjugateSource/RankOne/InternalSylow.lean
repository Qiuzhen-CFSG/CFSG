module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.SourceSylow

/-!
# Internal Baumann actors and the original Sylow intersection

An internal actor with the same root parameter differs by an element of
the full module centralizer. The source core decomposition therefore gives
Baum(S)=(Baum(S)∩L)C_S(L). Normal Sylow restriction and maximality identify
Baum(S)∩L with the original S∩L, including nonsplit central covers.

Source: Aschbacher–Smith, proof of 2.4.8(5), printed p.530, using C.5.4.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R L : Subgroup G} {F : Type*} [Field F]

theorem ActionCoordinates.internal_span (c : ActionCoordinates R L F)
    (hi : c.IsInternal) : S R ≤ (S R ⊓ L) ⊔ (S R ⊓ centralizer (U L : Set G)) := by
  intro s hs
  obtain ⟨t,ht,hp⟩ := hi ⟨s,hs⟩
  have hc : (t : G)⁻¹ * s ∈ centralizer (U L : Set G) := by
    apply (c.parameter_kernel (t⁻¹ * ⟨s,hs⟩)).mp
    simp only [map_mul,map_inv,hp,inv_mul_cancel]
  have hh := mul_mem_sup (show (t : G) ∈ S R ⊓ L from ⟨t.property,ht⟩)
    (show (t : G)⁻¹ * s ∈ S R ⊓ centralizer (U L : Set G) from
      ⟨(S R).mul_mem ((S R).inv_mem t.property) hs,hc⟩)
  simpa only [mul_inv_cancel_left] using hh

theorem Setup.internal_decomposition (h : Setup R L F) (hi : h.coordinates.IsInternal)
    (hc : S R ⊓ centralizer (U L : Set G) = U L ⊔ (R ⊓ centralizer (L : Set G))) :
    S R = (S R ⊓ L) ⊔ (R ⊓ centralizer (L : Set G)) := by
  have hD : R ⊓ centralizer (L : Set G) ≤ S R :=
    (le_sup_right.trans hc.ge).trans inf_le_left
  apply le_antisymm _ (sup_le inf_le_left hD)
  have hh := h.coordinates.internal_span hi
  rw [hc] at hh
  exact hh.trans (sup_le le_sup_left (sup_le
    ((le_inf h.module_le (map_subtype_le _)).trans le_sup_left) le_sup_right))

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

theorem Setup.source_sylow_intersection (h : Setup R L F) (hR : IsPGroup 2 R) :
    S R ⊓ L = R ⊓ L := by
  obtain ⟨P,hP⟩ := h.source_sylow_block hR
  let W := R.subgroupOf L
  have hPW : (P : Subgroup L) ≤ W := by
    intro x hx
    exact (show S R ≤ R from inf_le_left) ((hP ▸ mem_map_of_mem L.subtype hx).1)
  have he := P.is_maximal' hR.comap_subtype hPW
  have he' := congrArg (Subgroup.map L.subtype) he
  rw [hP,map_comap_eq,range_subtype] at he'
  exact he'.symm.trans (inf_comm _ _)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

