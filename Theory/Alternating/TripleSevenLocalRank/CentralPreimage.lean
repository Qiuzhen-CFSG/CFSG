module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.Quasithin.LocalRankEmbedding

/-!
# Restriction of a central extension to an actual subgroup

The inverse image of an injectively marked subgroup maps onto that subgroup.
Its kernel is canonically isomorphic to the original central kernel. This
preserves both centrality and exact kernel cardinality, and supplies the
literal preimages used for the alternating and Mathieu triple-cover local
rank obstructions in Aschbacher–Smith A.2.12(I.i), printed p.36.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.CubicCoverPreimage
open Subgroup
variable {E G K : Type*} [Group E] [Group G] [Group K]

/-- Restrict an actual central extension to an injectively marked subgroup. -/
theorem exists_restriction (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (j : K →* G) (hj : Function.Injective j) :
    ∃ (P : Subgroup E) (q : P →* K), Function.Surjective q ∧
      q.ker ≤ center P ∧ Nat.card q.ker = Nat.card f.ker := by
  let P := j.range.comap f
  let e : K ≃* j.range := MonoidHom.ofInjective hj
  let q : P →* K := e.symm.toMonoidHom.comp (f.subgroupComap j.range)
  have hq (x : P) : q x = 1 ↔ f (x : E) = 1 := by
    change e.symm (f.subgroupComap j.range x) = 1 ↔ _
    rw [e.symm.map_eq_one_iff]
    exact Subtype.ext_iff
  have hqs : Function.Surjective q := by
    intro k
    obtain ⟨x,hx⟩ := hf (j k)
    refine ⟨⟨x,show f x ∈ j.range by rw [hx]; exact ⟨k,rfl⟩⟩,?_⟩
    change e.symm ⟨f x,_⟩ = k
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext hx
  have hqc : q.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hc ((hq x).mp hx)) y
  let k : q.ker →* f.ker :=
    (P.subtype.comp q.ker.subtype).codRestrict _ (fun x => (hq x).mp x.prop)
  have hki : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : E)) h))
  have hks : Function.Surjective k := by
    intro x
    let y : P := ⟨x,show f (x : E) ∈ j.range by rw [x.prop]; exact one_mem _⟩
    exact ⟨⟨y,(hq y).mpr x.prop⟩,rfl⟩
  exact ⟨P,q,hqs,hqc,Nat.card_congr (MulEquiv.ofBijective k ⟨hki,hks⟩).toEquiv⟩

end Theory.GroupTheory.CubicCoverPreimage
