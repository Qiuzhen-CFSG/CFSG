module

public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Faithful Sylow lifts in central covers

A subgroup on which a quotient map is faithful inherits commutator generation
from its image. If its image is Sylow and the kernel is a p-group, its product
with the kernel is Sylow. In a p-perfect central cover, transfer then forces
the faithful subgroup to be the entire Sylow group, killing the kernel.

This supplies the transfer version of the central-cover argument in
Aschbacher–Smith G.2.3, printed pp.333–334, without a splitting theorem.
-/

public section
namespace Subgroup
variable {E Q : Type*} [Group E] [Group Q]

/-- Faithfulness lifts commutator generation by a normalizing actor. -/
theorem eq_commutator_of_faithful_image (f : E →* Q) (A C : Subgroup E)
    (hn : C ≤ normalizer (A : Set E)) (hf : Disjoint A f.ker)
    (hc : ⁅A.map f, C.map f⁆ = A.map f) : ⁅A, C⁆ = A := by
  have hle := le_normalizer_iff_commutator_le_left.mp hn
  have hinj : Set.InjOn f A := (Set.injOn_iff_map_eq_one f A).mpr
    (fun x hx hk => disjoint_def.mp hf hx hk)
  apply le_antisymm hle
  intro a ha
  have hm : f a ∈ (⁅A, C⁆).map f := by
    rw [map_commutator, hc]
    exact mem_map_of_mem f ha
  obtain ⟨b, hb, he⟩ := hm
  exact hinj (hle hb) ha he ▸ hb

variable [Finite E] {p : ℕ} [Fact p.Prime]

omit [Finite E] [Fact p.Prime] in
/-- The Sylow preimage is the supplement of the lifted subgroup by the kernel. -/
theorem exists_sylow_eq_sup_ker_of_sylow_image (f : E →* Q)
    (hp : IsPGroup p f.ker) (A : Subgroup E) (S : Sylow p Q)
    (hS : A.map f = S) : ∃ R : Sylow p E, (R : Subgroup E) = A ⊔ f.ker := by
  let R := S.comapOfKerIsPGroup f hp (by rw [← hS]; exact map_le_range (f := f) (H := A))
  refine ⟨R, ?_⟩
  change (S : Subgroup Q).comap f = A ⊔ f.ker
  rw [← hS, comap_map_eq]

omit [Finite E] [Fact p.Prime] in
/-- The faithful lift is a complement to the kernel in its Sylow preimage. -/
theorem exists_sylow_complement_of_faithful_image (f : E →* Q)
    (hp : IsPGroup p f.ker) (A : Subgroup E) (hA : Disjoint A f.ker)
    (S : Sylow p Q) (hS : A.map f = S) :
    ∃ R : Sylow p E, A ≤ R ∧
      (A.subgroupOf (R : Subgroup E)).IsComplement'
        (f.ker.subgroupOf (R : Subgroup E)) := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_sup_ker_of_sylow_image f hp A S hS
  have ha : A ≤ R := by rw [hR]; exact le_sup_left
  have hk : f.ker ≤ R := by rw [hR]; exact le_sup_right
  refine ⟨R, ha, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply disjoint_def.mpr
    intro x hx hxk
    exact Subtype.ext (disjoint_def.mp hA hx hxk)
  · rw [← coe_mul_of_left_le_normalizer_right _ _ le_normalizer_of_normal,
      ← subgroupOf_sup ha hk, ← hR, subgroupOf_self, coe_top]

/-- A faithful Sylow lift kills a central p-kernel in a p-perfect group. -/
theorem ker_eq_bot_of_faithful_sylow_image (hE : IsPPerfect p E)
    (f : E →* Q) (hc : f.ker ≤ center E) (hp : IsPGroup p f.ker)
    (A : Subgroup E) (hA : Disjoint A f.ker)
    (S : Sylow p Q) (hS : A.map f = S) : f.ker = ⊥ := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_sup_ker_of_sylow_image f hp A S hS
  have he : A = R := sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect
    hE R f hc A (by rw [hR]; exact le_sup_left) (by
      rw [hR, map_sup, map_ker_self, sup_bot_eq])
  apply eq_bot_iff.mpr
  intro x hx
  have hxR : x ∈ (R : Subgroup E) := by rw [hR]; exact mem_sup_right hx
  exact disjoint_def.mp hA (he.symm ▸ hxR) hx

end Subgroup
