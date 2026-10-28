module

public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Detecting a central kernel with a split Sylow lift

In a finite p-perfect group, transfer puts a central kernel in the
Frattini subgroup of every Sylow p-subgroup. A subgroup covering the
Sylow image therefore equals that Sylow subgroup. If the covering
subgroup is a product of two injectively mapped factors with disjoint
images, its intersection with the kernel is trivial.

This is the central-kernel step in Aschbacher–Smith G.2.5(3), printed
pp.335–336, using the transfer argument behind G.2.3 on pp.333–334.
The rank-three application must construct the second root factor: the
point radical alone is not a Sylow subgroup.
-/

public section
namespace Subgroup
open scoped Pointwise

variable {E Q : Type*} [Group E] [Group Q]

/-- A normalized product of faithful factors with disjoint images is faithful. -/
theorem disjoint_ker_sup_of_disjoint_images (f : E →* Q) (A B : Subgroup E)
    (hBA : B ≤ normalizer (A : Set E))
    (hA : Disjoint A f.ker) (hB : Disjoint B f.ker)
    (hAB : Disjoint (A.map f) (B.map f)) : Disjoint (A ⊔ B) f.ker := by
  apply disjoint_def.mpr
  intro x hx hk
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A B hBA] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have he : f a * f b = 1 := by simpa only [map_mul] using (MonoidHom.mem_ker.mp hk)
  have haB : f a ∈ B.map f := by
    rw [eq_inv_of_mul_eq_one_left he]
    exact (B.map f).inv_mem (mem_map_of_mem f hb)
  have ha1 : f a = 1 := disjoint_def.mp hAB (mem_map_of_mem f ha) haB
  have ha0 : a = 1 := disjoint_def.mp hA ha ha1
  have hb1 : f b = 1 := by simpa only [ha1, one_mul] using he
  have hb0 : b = 1 := disjoint_def.mp hB hb hb1
  simp only [ha0, hb0, mul_one]

/-- A two-factor Sylow lift kills a central p-kernel in a p-perfect group. -/
theorem ker_eq_bot_of_split_sylow_of_isPPerfect [Finite E]
    {p : ℕ} [Fact p.Prime] (hE : IsPPerfect p E)
    (f : E →* Q) (hc : f.ker ≤ center E) (hp : IsPGroup p f.ker)
    (R : Sylow p E) (A B : Subgroup E)
    (hAR : A ≤ R) (hBR : B ≤ R)
    (hBA : B ≤ normalizer (A : Set E))
    (hA : Disjoint A f.ker) (hB : Disjoint B f.ker)
    (hAB : Disjoint (A.map f) (B.map f))
    (hcover : (R : Subgroup E).map f ≤ A.map f ⊔ B.map f) : f.ker = ⊥ := by
  have he : A ⊔ B = R :=
    sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect hE R f hc
      (A ⊔ B) (sup_le hAR hBR) (by rwa [map_sup])
  have hdis := disjoint_ker_sup_of_disjoint_images f A B hBA hA hB hAB
  rw [he] at hdis
  apply eq_bot_iff.mpr
  intro x hx
  exact disjoint_def.mp hdis (hp.le_sylow_of_normal R hx) hx

end Subgroup
