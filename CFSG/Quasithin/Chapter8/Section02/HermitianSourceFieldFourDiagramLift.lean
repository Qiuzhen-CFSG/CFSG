module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalCoreTwoClosedTransport

/-!
# Lifting the actual Hermitian diagram witness

A marked automorphism moving a parabolic conjugacy class is noninner.
When the full source core is trivial, its literal quotient action lifts to
an element of the original marked subgroup acting on the full component.
The lift uses the same recognition map and preserves conjugation orientation.
A separate normal-core calculation applies this to H/O₂(H).

Source: Aschbacher–Smith E.2.2(2b), printed p.215, and 8.2.9,
printed p.721, refs/quasithin.pdf. The chosen-module consumer keeps the
original maximal overlap and Sylow subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X]
set_option backward.isDefEq.respectTransparency false

private theorem movesDiagram_has_outer {M K T : Subgroup X} {D : Type*} [Group D]
    (e : sourceImage M K ≃* D) (P Q : Subgroup D)
    (h : MovesDiagram M K T e P Q) :
    ∃ a ∈ sourceAutomizer M K T, a ∉ MulAut.innerSubgroup (sourceImage M K) := by
  obtain ⟨a,ha,hm⟩ := h
  refine ⟨a,ha,?_⟩
  rintro ⟨g,rfl⟩
  apply hm
  rw [MulAut.congr_conj]
  exact ⟨⟨e g,rfl⟩,⟨e g,rfl⟩⟩

/-- The literal diagram witness lifts to a noninner action of an element of
its original marked subgroup on the full component, when the source core
is trivial. Both diagram-model branches use their own recognition map. -/
theorem corefree_diagram_actor_lift
    (M K T : Subgroup X) [K.Normal] {n : ℕ}
    (hcore : sourceKernel M = ⊥) (hd : DiagramModel M K T n) :
    ∃ t : T, ∃ α : MulAut K, α ∉ MulAut.innerSubgroup K ∧
      (∀ k : K, (α k : X) = (t : X) * (k : X) * (t : X)⁻¹) := by
  have houter : ∃ a ∈ sourceAutomizer M K T,
      a ∉ MulAut.innerSubgroup (sourceImage M K) := by
    rcases hd with h | h
    all_goals
      obtain ⟨F,hF,hfin,hchar,hn,hcard,e,hB,hm⟩ := h
      exact movesDiagram_has_outer e _ _ hm
  obtain ⟨a,ha,hane⟩ := houter
  obtain ⟨x,hx,hxa⟩ := ha
  obtain ⟨t,ht,hxt⟩ := hx
  let q := QuotientGroup.mk' (sourceKernel M)
  have hqi : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk',hcore]
  let e : K ≃* sourceImage M K := MulEquiv.ofBijective (q.subgroupMap K)
    ⟨fun x y he => Subtype.ext (hqi (congrArg Subtype.val he)),q.subgroupMap_surjective K⟩
  let α : MulAut K := MulAut.conjNormal t
  have he : MulAut.congr e α = a := by
    apply MulEquiv.ext
    intro y
    obtain ⟨k,rfl⟩ := e.surjective y
    change e (α (e.symm (e k))) = a (e k)
    rw [e.symm_apply_apply,←hxa]
    apply Subtype.ext
    change q (t * (k : X) * t⁻¹) = (x : X ⧸ sourceKernel M) * q k * (x : X ⧸ sourceKernel M)⁻¹
    have hxt' : q t = (x : X ⧸ sourceKernel M) := hxt
    rw [←hxt',map_mul,map_mul,map_inv]
  refine ⟨⟨t,ht⟩,α,?_,fun k => rfl⟩
  intro hi
  apply hane
  rw [←he,←MulAut.map_innerSubgroup_congr e]
  exact mem_map_of_mem (MulAut.congr e).toMonoidHom hi

/-- Quotienting a maximal subgroup by its entire normal core leaves a
core-free image. This keeps the original quotient map in the diagram lift. -/
theorem image_normalCore_eq_bot (M N : Subgroup X) [N.Normal]
    (hcore : M.normalCore = N) :
    (M.map (QuotientGroup.mk' N)).normalCore = ⊥ := by
  let q := QuotientGroup.mk' N
  have hk : q.ker ≤ M := by rw [QuotientGroup.ker_mk',←hcore]; exact M.normalCore_le
  have hc : (M.map q).comap q = M := by rw [comap_map_eq,sup_eq_left.mpr hk]
  apply (comap_injective (QuotientGroup.mk'_surjective N))
  rw [←normalCore_comap_of_surjective q (QuotientGroup.mk'_surjective N),hc,hcore]
  exact (QuotientGroup.ker_mk' N).symm
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
