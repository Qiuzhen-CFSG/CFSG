module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersectionsTransitivity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# A pure HS sixteen-subgroup escapes every one of its point cores

After marking the pure elementary sixteen-subgroup and a nonidentity point,
one row witnesses failure of containment in the actual involution-centralizer
two-core: the marked involution fixes letter2, but the witness sends that
letter to77 rather than2 or its paired letter58. The native pair kernel is
the full intrinsic two-core. Conjugation transports that obstruction while
retaining the actual subgroup and actual point centralizer.

Source: the HS inspection in Aschbacher--Smith12.6.12, printed pp.825--826,
and the central-involution local in GLS3 Table5.3m. No exclusion or closure
hypothesis is supplied to the public theorem.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsGlobalNative
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
open EvenLocalCandidates.CentralInvolutionCore
open OriginalHigmanSimsImageIntersectionsNative

private theorem marked_not_le_point_core :
    ¬ markedW ≤ (centralizer ({e0} : Set Carrier)).pCoreIn 2 := by
  intro h
  have hx : element 11 ∈ markedW := by
    refine ⟨3,?_⟩
    have hr : candidateRow 0 3 = 11 := by decide +kernel
    change element (candidateRow 0 3) = element 11
    rw [hr]
  have hc := h hx
  rw [←LocalGeneration.first_eq_centralizer] at hc
  obtain ⟨x,hxcore,hxe⟩ := hc
  have hm : x ∈ core := LocalGeneration.first_core_eq ▸ hxcore
  have hh := (mem_core_iff x).mp hm 2 (by decide +kernel)
  have hv := congrArg (fun a : Carrier => (a : Equiv.Perm (Fin 100)) 2) hxe
  change x.val.val 2 = (element 11 : Equiv.Perm (Fin 100)) 2 at hv
  rw [hv] at hh
  have hn : ¬ ((element 11 : Equiv.Perm (Fin 100)) 2 = 2 ∨
      (element 11 : Equiv.Perm (Fin 100)) 2 = twin 2) := by decide +kernel
  exact hn hh

/-- A pure elementary sixteen-subgroup of the actual HS carrier is not
contained in the full two-core of the centralizer of any of its nonidentity
points. Purity refers to the original degree100 action. -/
theorem pure_sixteen_not_le_point_core
    (W : Subgroup Carrier) (hW : IsElementaryAbelian 2 W) (hcard : Nat.card W = 16)
    (hp : ∀ x ∈ W, ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p)
    (j : Carrier) (hj : j ∈ W) (hne : j ≠ 1) :
    ¬ W ≤ (centralizer ({j} : Set Carrier)).pCoreIn 2 := by
  obtain ⟨g,hg⟩ := pure_sixteen_conjugate W hW hcard hp
  have hjW : (MulAut.conj g) j ∈ markedW := hg ▸ mem_map_of_mem _ hj
  have hjne : (MulAut.conj g) j ≠ 1 := by
    intro he
    exact hne ((MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨k,hk,hkj⟩ := markedW_point_transitive _ hjW hjne
  let α : MulAut Carrier := MulAut.conj k * MulAut.conj g
  have hmark : W.map α.toMonoidHom = markedW := by
    change W.map ((MulAut.conj k).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = markedW
    rw [←Subgroup.map_map,hg]
    exact mem_normalizer_iff_map_conj_eq.mp hk
  have hpoint : α j = e0 := hkj
  have hcent : (centralizer ({j} : Set Carrier)).map α.toMonoidHom =
      centralizer ({e0} : Set Carrier) := by
    rw [map_centralizer_equiv,Set.image_singleton,hpoint]
  intro h
  have hm := map_mono (f := α.toMonoidHom) h
  rw [hmark,map_pCoreIn_of_injective 2 _ _ α.injective,hcent] at hm
  exact marked_not_le_point_core hm

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsGlobalNative
