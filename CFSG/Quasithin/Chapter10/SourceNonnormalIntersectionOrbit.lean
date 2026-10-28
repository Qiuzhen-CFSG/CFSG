module
public import CFSG.Quasithin.Chapter10.SourceNonnormalIntersectionComponent
public import Theory.GroupTheory.PResidual.OrbitCoverIntersection

/-!
# The orbit of the literal intersection component

In the original Fundamental Setup, a subgroup I covering L₀ modulo its
two-core and retaining the original component orbit supplies the exact
C.2.8 generator identity: the (H ∩ M)-span of (L ∩ H)^∞ equals
O²(L₀ ∩ H). The intersection-cover theorem supplies the individual
component cover; its intrinsic two-core lies in O₂(L₀) by subnormality.
The general conjugate-span residual theorem then gives the equality.

Source: Aschbacher–Smith, 4.2.4 and its use in 4.2.12, combined
manuscript of 1 March 2004, printed pp.608 and 610. No C.4.8 normality
consequence or normality of the original component is assumed here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- Retaining the original component orbit gives the literal C.2.8
generation identity in the intersection. -/
theorem source_covering_intersection_orbit
    {I H : Subgroup G} (hIM : I ≤ D.maximalLocal) (hIH : I ≤ H)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (horbit : componentOrbit L I = localOrbit T L) :
    conjugateSpanBy
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (H ⊓ D.maximalLocal) =
        (pResidual 2 (localOrbit T L ⊓ H : Subgroup G)).map
          (localOrbit T L ⊓ H).subtype := by
  let X := localOrbit T L
  let M := D.maximalLocal
  let U := H ⊓ M
  let A := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLX : L ≤ X := le_componentOrbit L T
  have hXM : X ≤ M := X.le_normalizer
  have hAX : A ≤ X := (map_subtype_le _).trans (inf_le_left.trans hLX)
  have hAU : A ≤ U := le_inf ((map_subtype_le _).trans inf_le_right)
    (hAX.trans hXM)
  have hLC : L.pCoreIn 2 ≤ X.pCoreIn 2 := by
    have hcomponent := D.component_in_maximalLocal.subgroupOf_of_le hLX hXM
    have hh := map_mono (f := X.subtype)
      (pCoreIn_le_of_subnormal 2 hcomponent.subnormal)
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,
      map_subgroupOf_eq_of_le hLX] at hh
    exact hh
  have hc : L ≤ A ⊔ X.pCoreIn 2 := by
    intro l hl
    obtain ⟨a,ha,n,hn,rfl⟩ := (source_covering_intersection_component D hIM hIH hcover).2.subset hl
    exact mul_mem_sup ha (hLC hn)
  have ho : conjugateSpanBy L I = X := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact horbit
  let : Group.IsPerfect A := Group.IsPerfect.map (L ⊓ H).subtype
  have he := conjugateSpanBy_eq_pResidual_intersection_of_core_cover
    hAX hAU (show U ≤ normalizer (X : Set G) from inf_le_right)
    (le_inf hIH hIM) ho hc
  have hi : X ⊓ U = X ⊓ H := by
    ext x
    exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,hXM h.1⟩⟩
  rw [hi] at he
  exact he
end CFSG.Quasithin.Chapter10
