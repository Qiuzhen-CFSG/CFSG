module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.CentralizerRank
public import Theory.SpecificGroups.PSL3Two.PairedSylowRecognition
public import Theory.SpecificGroups.PSL3Two.PairedGraphCentralizerRank
public import Theory.SpecificGroups.PSL3Two.PairedAmbientTransfer

/-!
# A faithful paired model retaining the source involution marks

The data keeps the original component and Sylow subgroup as literal images
of the two base factors and standard paired Sylow. Its graph actor fixes S₃
on the original component and has ambient centralizer of three-rank at least
two. These statements supply the nonfusion calculations in the proof of
Aschbacher--Smith 2.4.34, printed p.548; the source constructor separately
produces the marked embedding from the contradictory centralization.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.PairedInvolutiveExtension
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.PairedGraphInputs Matrix.PSL3Two.PairedSylowRecognition
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G]
variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
variable {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)

/-- The faithful paired model with the original component, Sylow subgroup,
and two source involutions retained literally. -/
structure SourcePairedEmbedding (K : Subgroup (involutionCentralizer g.z₂)) where
  f : StandardModel →* G
  injective : Function.Injective f
  sylowEquiv : standardPaired ≃* T
  sylow_spec : ∀ u : standardPaired, f u.val = (sylowEquiv u : G)
  componentEquiv : K ≃* SL
  first_eval : ∀ k : SL, f (base diagram diagram_involutive k 1) =
    ((componentEquiv.symm k : involutionCentralizer g.z₂) : G)
  first_mark : f (base diagram diagram_involutive highestRoot 1) = g.z₁
  second_mark : f (base diagram diagram_involutive 1 highestRoot) = g.z₂

namespace SourcePairedEmbedding
variable {g} {K : Subgroup (involutionCentralizer g.z₂)} (m : SourcePairedEmbedding g K)

omit [Finite G] in
theorem product_mark : m.f (base diagram diagram_involutive highestRoot highestRoot) = g.z₁*g.z₂ := by
  rw [← m.first_mark, ← m.second_mark, ← map_mul]
  apply congrArg m.f
  simp [base]

include m in
omit [Finite G] in
theorem first_mem : ∃ hz : g.z₁ ∈ involutionCentralizer g.z₂,
    (⟨g.z₁,hz⟩ : involutionCentralizer g.z₂) ∈ K := by
  have he : (((m.componentEquiv.symm highestRoot : K) : involutionCentralizer g.z₂) : G) = g.z₁ :=
    (m.first_eval highestRoot).symm.trans m.first_mark
  have hh := (m.componentEquiv.symm highestRoot).property
  exact ⟨he ▸ (m.componentEquiv.symm highestRoot).val.property, by simpa only [← he] using hh⟩

omit [Finite G] in
theorem graph_mem_second : m.f (graph diagram diagram_involutive) ∈ involutionCentralizer g.z₂ := by
  apply mem_centralizer_singleton_iff.mpr
  rw [← m.second_mark, ← map_mul, ← map_mul]
  apply congrArg m.f
  exact (mem_centralizer_singleton_iff.mp
    ((mem_centralizer_graph_mk diagram diagram_involutive 1 highestRoot 1 1).mpr
      ⟨diagram.fixedSubgroup.one_mem, (MulAut.mem_fixedSubgroup diagram highestRoot).mpr diagram_highestRoot⟩)).symm

omit [Finite G] in
private theorem first_commutes_graph_iff (a : SL) :
    Commute (m.f (base diagram diagram_involutive a 1)) (m.f (graph diagram diagram_involutive)) ↔
      a ∈ diagram.fixedSubgroup := by
  rw [Commute, SemiconjBy]
  rw [← map_mul, ← map_mul, m.injective.eq_iff]
  simpa only [base, mk, mem_centralizer_singleton_iff, one_mem, and_true] using
    (mem_centralizer_graph_mk diagram diagram_involutive a 1 1 1)

/-- The chosen graph actor fixes precisely S₃ on the original component. -/
noncomputable def componentFixedEquiv :
    K.subgroupOf (centralizer ({(⟨m.f (graph diagram diagram_involutive), m.graph_mem_second⟩ :
      involutionCentralizer g.z₂)} : Set (involutionCentralizer g.z₂))) ≃* Equiv.Perm (Fin 3) := by
  let x : involutionCentralizer g.z₂ := ⟨m.f (graph diagram diagram_involutive),m.graph_mem_second⟩
  let C := centralizer ({x} : Set (involutionCentralizer g.z₂))
  let e : K.subgroupOf C ≃* diagram.fixedSubgroup :=
    { toFun := fun a => ⟨m.componentEquiv ⟨a.val.val,a.property⟩, by
        apply (m.first_commutes_graph_iff _).mp
        rw [m.first_eval, MulEquiv.symm_apply_apply]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.val.property)⟩
      invFun := fun a => ⟨⟨(m.componentEquiv.symm a : involutionCentralizer g.z₂), by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        have hh := (m.first_commutes_graph_iff a).mpr a.property
        rw [m.first_eval] at hh
        exact hh⟩, (m.componentEquiv.symm a).property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        change ((m.componentEquiv.symm (m.componentEquiv ⟨a.val.val,a.property⟩) : K) : involutionCentralizer g.z₂) = a.val.val
        exact congrArg Subtype.val (m.componentEquiv.symm_apply_apply ⟨a.val.val,a.property⟩)
      right_inv := by intro a; apply Subtype.ext; exact m.componentEquiv.apply_symm_apply a
      map_mul' := by
        intro a b
        apply Subtype.ext
        change m.componentEquiv ((⟨a.val.val,a.property⟩ : K) * ⟨b.val.val,b.property⟩) = _
        exact m.componentEquiv.map_mul _ _ }
  exact e.trans fixedEquivSymmetricThree

/-- Both independent cubic fixed subgroups embed in the ambient graph centralizer. -/
theorem graph_three_rank : 2 ≤ primeRank 3 (centralizer ({m.f (graph diagram diagram_involutive)} : Set G)) := by
  let C := centralizer ({graph diagram diagram_involutive} : Set StandardModel)
  let f : C →* centralizer ({m.f (graph diagram diagram_involutive)} : Set G) :=
    { toFun := fun a => ⟨m.f a, mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul]
        exact congrArg m.f (mem_centralizer_singleton_iff.mp a.property))⟩
      map_one' := Subtype.ext m.f.map_one
      map_mul' := fun a b => Subtype.ext (m.f.map_mul a b) }
  exact (Matrix.PSL3Two.PairedGraphCentralizerRank.two_le_threeRank diagram diagram_involutive diagram_ne_conj).trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 f (fun a b h => Subtype.ext (m.injective (congrArg Subtype.val h))))

end SourcePairedEmbedding
end CFSG.Quasithin.Chapter2.DoubleA3
