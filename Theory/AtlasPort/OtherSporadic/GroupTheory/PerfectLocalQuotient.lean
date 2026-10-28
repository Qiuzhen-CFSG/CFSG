/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PerfectLocalQuotient.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Perfect local quotients and normal subgroups

An abelian homomorphism absorbing the kernel of a perfect quotient vanishes.
A normal subgroup with suitable local factorization is therefore the whole
group, by applying this fact to its quotient map.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PerfectLocalQuotient.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

open scoped commutatorElement

namespace Atlas.GroupTheory

/-- A homomorphism to an abelian group vanishes if it factors through a
surjective perfect quotient. This retains the kernel rather than assuming the
original group itself perfect. -/
theorem hom_trivial_of_perfect_quotient {K A B : Type*} [Group K] [Group A] [CommGroup B]
    (f : K →* A) (q : K →* B) (hf : Function.Surjective f)
    (hA : commutator A=⊤) (hker : f.ker ≤ q.ker) : ∀ k, q k=1 := by
  have hm : (commutator K).map f=⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,← commutator_def,hA]
  intro k
  have hk : f k ∈ (commutator K).map f := by rw [hm]; trivial
  obtain ⟨c,hc,hck⟩ := hk
  have hq : q c=1 := Abelianization.commutator_subset_ker q hc
  have hfc : c⁻¹*k ∈ f.ker := by
    change f (c⁻¹*k)=1
    simp only [map_mul,map_inv,hck,inv_mul_cancel]
  have hqc : q (c⁻¹*k)=1 := hker hfc
  simpa only [map_mul,map_inv,hq,inv_one,one_mul] using hqc

end Atlas.GroupTheory

namespace Atlas.GroupTheory

/-- A normal subgroup exhausting the ambient group modulo a small local group
is the whole group when that local image is abelian and is contained in a local
group with a perfect quotient whose kernel is already absorbed. -/
theorem normal_eq_top_of_local_quotients {G H K A : Type*}
    [Group G] [Group H] [Group K] [Group A]
    (N : Subgroup G) [N.Normal] (i : H →* G) (j : K →* G) (f : K →* A)
    (hf : Function.Surjective f) (hA : commutator A=⊤)
    (hfactor : ∀ g : G, ∃ n : N, ∃ h : H, g=n.val*i h)
    (hcomm : ∀ h h' : H, ⁅i h,i h'⁆ ∈ N)
    (hker : ∀ k ∈ f.ker, j k ∈ N)
    (hlocal : ∀ h : H, ∃ k : K, j k=i h) : N=⊤ := by
  let q := QuotientGroup.mk' N
  have hsur : Function.Surjective (q.comp i) := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨n,h,rfl⟩ := hfactor g
    refine ⟨h,?_⟩
    change q (i h)=q (n.val*i h)
    rw [map_mul,show q n.val=1 from (QuotientGroup.eq_one_iff _).mpr n.prop,one_mul]
  have hc : ∀ x y : G ⧸ N, x*y=y*x := by
    intro x y
    obtain ⟨h,rfl⟩ := hsur x
    obtain ⟨h',rfl⟩ := hsur y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅q (i h),q (i h')⁆=1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm h h')
  let : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hc }
  have hz : ∀ k, q (j k)=1 := hom_trivial_of_perfect_quotient f (q.comp j) hf hA
    (fun k hk => (QuotientGroup.eq_one_iff _).mpr (hker k hk))
  apply top_unique
  intro g _
  obtain ⟨n,h,rfl⟩ := hfactor g
  obtain ⟨k,hk⟩ := hlocal h
  apply N.mul_mem n.prop
  exact (QuotientGroup.eq_one_iff _).mp (hk ▸ hz k)

end Atlas.GroupTheory
