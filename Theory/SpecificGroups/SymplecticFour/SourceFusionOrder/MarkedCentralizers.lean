module
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.ElementCentralizer
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Root centralizers and marked comparisons

For each nonidentity element of either local center in Sp4 over a field
of even order greater than two, the full native centralizer is the local
subgroup. The point calculation uses the root matrices; the exceptional
graph automorphism gives the plane calculation. An injective local map
then identifies full ambient centralizers when both containments hold,
retaining the original map on every element.

Source: the symplectic root-centralizer step of Aschbacher--Smith
F.4.31(c), F.4.42--43, printed pp.291,295--296 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem root_element_centralizer (r : Fin 8) {t : F} (ht : t≠0) :
    centralizer ({rootElement r t} : Set (Sp F)) =
      centralizer ((RootSubgroup.group r : Subgroup (Sp F)) : Set (Sp F)) := by
  apply le_antisymm
  · intro g hg x hx
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
    exact (RootSubgroup.commute_element_of_ne_zero r ht g
      (mem_centralizer_singleton_iff.mp hg) s).symm.eq
  · exact centralizer_le (Set.singleton_subset_iff.mpr
      ((RootSubgroup.mem_group_iff r _).mpr ⟨t,rfl⟩))

theorem point_center_element_centralizer {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (z : Sp F) (hz : z∈(center (pointLocal (F := F))).map pointLocal.subtype) (hne : z≠1) :
    centralizer ({z} : Set (Sp F))=pointLocal := by
  rw [PointRadicalAction.center_eq_root hF hn] at hz
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 z).mp hz
  have ht : t≠0 := fun ht => hne (ht ▸ RootSubgroup.element_zero 0)
  rw [root_element_centralizer 0 ht,RootNormalizerResidual.centralizer_zero_eq]

theorem plane_center_element_centralizer {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (z : Sp F) (hz : z∈(center (planeLocal (F := F))).map planeLocal.subtype) (hne : z≠1) :
    centralizer ({z} : Set (Sp F))=planeLocal := by
  let a := DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
  let e : pointParabolic (F := F) ≃* planeParabolic := (a.subgroupMap pointParabolic).trans
    (MulEquiv.subgroupCongr DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point)
  have hmap : (pointLocal (F := F)).map a.toMonoidHom = planeLocal := by
    rw [←pointParabolic_solvableResidual_eq hF hn,map_map]
    change (solvableResidual (pointParabolic (F := F))).map
      (planeParabolic.subtype.comp e.toMonoidHom) = planeLocal
    rw [←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact planeParabolic_solvableResidual_eq hF hn
  have hc := map_subgroup_center_eq a.toMonoidHom a.injective (pointLocal (F := F))
  rw [hmap] at hc
  rw [←hc] at hz
  obtain ⟨x,hx,rfl⟩ := hz
  have hx1 : x≠1 := a.map_ne_one_iff.mp hne
  have hh := CentralizerSmallKernelTransport.map_centralizer a x
  rw [point_center_element_centralizer hF hn x hx hx1] at hh
  exact hh.symm.trans hmap

end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {G J : Type*} [Group G] [Group J]

/-- An ambient centralizer comparison retaining the specified local map pointwise. -/
@[expose] def MarkedCentralizerComparison (M : Subgroup G) (φ : M→*J) (z : M) : Prop :=
  ∃ hz : centralizer ({z.val} : Set G)≤M,
    ∃ e : centralizer ({z.val} : Set G)≃*centralizer ({φ z} : Set J),
      ∀ x, (e x).val=φ (inclusion hz x)

/-- Restriction of an injective local map identifies the full centralizers
when both ambient containments have been proved. -/
theorem marked_centralizer_comparison (M : Subgroup G) (φ : M→*J)
    (hφ : Function.Injective φ) (z : M)
    (hz : centralizer ({z.val} : Set G)≤M)
    (hw : centralizer ({φ z} : Set J)≤φ.range) :
    MarkedCentralizerComparison M φ z := by
  let f : centralizer ({z.val} : Set G)→*centralizer ({φ z} : Set J) :=
    (φ.comp (inclusion hz)).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      have hh : inclusion hz x*z=z*inclusion hz x :=
        Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
      simpa only [MonoidHom.comp_apply,map_mul] using congrArg φ hh)
  have hf : Function.Injective f := by
    intro x y he
    exact (inclusion_injective hz) (hφ (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hw y.property
    have hxc : x.val∈centralizer ({z.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have heq : x*z=z*x := hφ (by
        rw [map_mul,map_mul,hx]
        exact mem_centralizer_singleton_iff.mp y.property)
      exact congrArg (fun v : M => v.val) heq
    exact ⟨⟨x.val,hxc⟩,Subtype.ext hx⟩
  exact ⟨hz,MulEquiv.ofBijective f ⟨hf,hs⟩,fun x => rfl⟩
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
