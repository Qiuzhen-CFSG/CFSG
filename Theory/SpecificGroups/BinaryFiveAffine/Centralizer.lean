module
public import Theory.SpecificGroups.BinaryFiveAffine.Embeddings
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic
/-!
# The marked involution centralizer is D₈ × S₄

The explicit commuting embeddings have disjoint images and orders eight
and twenty-four. The centralizer of the marked pair vector has order
16 · 12: the vector group is unrestricted and its permutation stabilizer
preserves a two-point set. Equality of these actual subgroups gives the
multiplication equivalence, retaining the marked involution in D₈.

Source: Aschbacher–Smith 13.9.10, the natural five-point branch.
-/
@[expose] public section
namespace BinaryFiveAffine
open Subgroup

def pairStabilizer : Subgroup S where
  carrier := {g | action g pair01 = pair01}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change action g pair01 = pair01 at hg
    change action h pair01 = pair01 at hh
    change action (g*h) pair01 = pair01
    rw [map_mul, MulAut.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change action g pair01 = pair01 at hg
    change action g⁻¹ pair01 = pair01
    apply (action g).injective
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, hg]

instance : DecidablePred (· ∈ pairStabilizer) := fun g =>
  inferInstanceAs (Decidable (action g pair01 = pair01))
instance : Fintype pairStabilizer := Subtype.fintype _

def centralizerCoordinates : centralizer ≃ V × pairStabilizer where
  toFun w := ⟨w.val.left, ⟨w.val.right, (mem_centralizer_iff w.val).mp w.property⟩⟩
  invFun p := ⟨⟨p.1, p.2.val⟩, (mem_centralizer_iff _).mpr p.2.property⟩
  left_inv w := by apply Subtype.ext; rfl
  right_inv p := rfl

theorem card_vectors : Nat.card V = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
theorem card_pairStabilizer : Nat.card pairStabilizer = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_centralizer : Nat.card centralizer = 192 := by
  rw [Nat.card_congr centralizerCoordinates, Nat.card_prod, card_vectors, card_pairStabilizer]

def R : Subgroup W := dihedralEmbedding.range
def X : Subgroup W := symmetricEmbedding.range

theorem R_le_centralizer : R ≤ centralizer := by
  rintro _ ⟨r, rfl⟩
  change dihedralEmbedding r ∈ Subgroup.centralizer ({t} : Set W)
  rw [Subgroup.mem_centralizer_singleton_iff, ← dihedral_marked, ← map_mul, ← map_mul]
  have hc : ∀ r : DihedralGroup 4, r * .r 2 = .r 2 * r := by decide +kernel
  rw [hc]

theorem X_le_centralizer : X ≤ centralizer := by
  rintro _ ⟨s,rfl⟩
  change symmetricEmbedding s ∈ Subgroup.centralizer ({t} : Set W)
  rw [Subgroup.mem_centralizer_singleton_iff, ← dihedral_marked]
  exact (embeddings_commute (.r 2) s).symm.eq

theorem R_centralizes_X : R ≤ Subgroup.centralizer (X : Set W) := by
  rintro _ ⟨r,rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨s,rfl⟩
  exact (embeddings_commute r s).symm.eq

set_option maxRecDepth 10000 in
theorem disjoint_factors : Disjoint R X := by
  apply disjoint_iff_inf_le.mpr
  rintro w ⟨⟨r,hr⟩,⟨s,hs⟩⟩
  have he := hr.trans hs.symm
  have hc : ∀ r : DihedralGroup 4, ∀ s : Equiv.Perm (Fin 4),
      (dihedralRaw r).left = (symmetricRaw s).left →
      (dihedralRaw r).right = (symmetricRaw s).right → r = 1 := by decide +kernel
  have hr1 := hc r s (congrArg SemidirectProduct.left he) (congrArg SemidirectProduct.right he)
  rw [hr1, map_one] at hr
  exact hr.symm

def productMap : DihedralGroup 4 × Equiv.Perm (Fin 4) →* W :=
  dihedralEmbedding.noncommCoprod symmetricEmbedding embeddings_commute

theorem productMap_injective : Function.Injective productMap :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨dihedralEmbedding_injective, symmetricEmbedding_injective, disjoint_factors⟩

theorem productMap_range : productMap.range = centralizer := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨p,rfl⟩
    exact centralizer.mul_mem (R_le_centralizer ⟨p.1,rfl⟩) (X_le_centralizer ⟨p.2,rfl⟩)
  · rw [← Nat.card_congr (MonoidHom.ofInjective productMap_injective).toEquiv,
      Nat.card_prod, card_centralizer]
    norm_num [DihedralGroup.card, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

noncomputable def productEquiv : DihedralGroup 4 × Equiv.Perm (Fin 4) ≃* centralizer :=
  (MonoidHom.ofInjective productMap_injective).trans (MulEquiv.subgroupCongr productMap_range)

noncomputable def dihedralEquiv : DihedralGroup 4 ≃* R := MonoidHom.ofInjective dihedralEmbedding_injective
noncomputable def symmetricEquiv : Equiv.Perm (Fin 4) ≃* X := MonoidHom.ofInjective symmetricEmbedding_injective
noncomputable def split : centralizer ≃* R × X :=
  productEquiv.symm.trans (dihedralEquiv.prodCongr symmetricEquiv)

theorem productEquiv_val (r : DihedralGroup 4) (s : Equiv.Perm (Fin 4)) :
    (productEquiv (r,s)).val = dihedralEmbedding r * symmetricEmbedding s := rfl

theorem split_coordinates (c : centralizer) :
    (split c).1.val * (split c).2.val = c.val := by
  have hc := congrArg Subtype.val (productEquiv.apply_symm_apply c)
  exact hc

theorem t_mem_R : t ∈ R := ⟨.r 2, dihedral_marked⟩

end BinaryFiveAffine
