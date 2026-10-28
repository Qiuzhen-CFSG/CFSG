module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Vertices
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer

/-!
# The S₃ vertex overlap and its maximality in the local A₅

The intrinsic cubic normalizer calculation is transported through the published
`vertexOverlapEquiv`. The two S₃ identifications preserve the literal ambient
embedding. Maximality is transported through `vertex_overlap`, supplying the
`hmax` premise of the parent's `localDataOfCalculations`.

The EdgeFrame applications use `endpoints_le` with explicit identifications of
the edge fixer and the literal local subgroup K with A₅. Constructing those
identifications remains with the source assembly owner. The noncentral overlap
needed there is already supplied by `vertex_overlap_not_le_centralizer` in `Vertices.lean`
(in the `AlternatingFiveGeometry` and `EdgeFrame` namespaces).

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section

open Subgroup
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
open alternatingGroup.FiveLocalGeometry
variable {G : Type*} [Group G] [Finite G]

namespace AlternatingFiveGeometry
variable (D : Seed G) (K : Subgroup G)

/-- Both identifications retain the normalizer's literal embedding in G. -/
theorem exists_vertex_overlap_equivs (eK : K ≃* alternatingGroup (Fin 5))
    (hX : D.X ≤ K) :
    ∃ eN : normalizer (D.X.subgroupOf K : Set K) ≃* Equiv.Perm (Fin 3),
      ∃ eV : ↥(K ⊓ normalizer (D.X : Set G)) ≃* Equiv.Perm (Fin 3),
        ∀ x : ↥(K ⊓ normalizer (D.X : Set G)), (((eN.symm (eV x)) : K) : G) = x := by
  have hc : Nat.card (D.X.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv, D.card_X]
  obtain ⟨eN⟩ := cubic_normalizer_equiv eK (D.X.subgroupOf K) hc
  refine ⟨eN, (vertexOverlapEquiv D K hX).trans eN, ?_⟩
  intro x
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
    vertexOverlapEquiv_coe D K hX x

/-- The actual ambient vertex overlap is S₃. -/
theorem vertex_overlap_equiv (eK : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K) :
    Nonempty (↥(K ⊓ normalizer (D.X : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨_, eV, _⟩ := exists_vertex_overlap_equivs D K eK hX
  exact ⟨eV⟩

omit [Finite G] in
private theorem map_covBy_subtype {L : Subgroup K} (hL : L ⋖ ⊤) :
    L.map K.subtype ⋖ K := by
  have ht : (⊤ : Subgroup K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hlt := (map_lt_map_iff_of_injective K.subtype_injective).mpr hL.lt
  rw [ht] at hlt
  refine ⟨hlt, ?_⟩
  intro U hLU hUK
  apply hL.2 (c := U.subgroupOf K)
  · apply (map_lt_map_iff_of_injective K.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hUK.le]
    exact hLU
  · apply (map_lt_map_iff_of_injective K.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hUK.le, ht]
    exact hUK

/-- This supplies the literal `hmax` input of `localDataOfCalculations`. -/
theorem vertex_overlap_maximal (eK : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K) :
    K ⊓ normalizer (D.X : Set G) ⋖ K := by
  have hc : Nat.card (D.X.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv, D.card_X]
  rw [vertex_overlap D K hX]
  exact map_covBy_subtype K (cubic_normalizer_maximal eK (D.X.subgroupOf K) hc)

end AlternatingFiveGeometry

namespace EdgeFrame
variable {D : Seed G} (F : EdgeFrame D)

/-- The marked edge endpoints put X inside the actual local A₅. -/
theorem vertex_overlap_equiv
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    Nonempty (↥(F.K ⊓ normalizer (D.X : Set G)) ≃* Equiv.Perm (Fin 3)) :=
  AlternatingFiveGeometry.vertex_overlap_equiv D F.K eK
    (le_sup_left.trans (F.endpoints_le he))

/-- Maximality in the literal centralizer K of the marked dihedral subgroup. -/
theorem vertex_overlap_maximal
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    F.K ⊓ normalizer (D.X : Set G) ⋖ F.K :=
  AlternatingFiveGeometry.vertex_overlap_maximal D F.K eK
    (le_sup_left.trans (F.endpoints_le he))

end EdgeFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
