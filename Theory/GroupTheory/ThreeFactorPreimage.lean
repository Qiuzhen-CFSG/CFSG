module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Lifting a three-factor product through a group homomorphism

A product of two image subgroups lifts to a three-factor product if the kernel
is covered by their kernel intersections and a third kernel subgroup. The
kernel must normalize the middle factor; this permits collecting the lifted
factors in the prescribed order. Consequently this set product is the join.

This is the elementary collection step used with the kernel decomposition in
Aschbacher--Smith G.2.5(3), in the last paragraph of 14.4.7 (printed p.1009).
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A product in the image lifts when its kernel has the indicated three
factors. Kernel normalization of the middle factor permits collecting terms. -/
theorem comap_eq_threeFactor (f : G →* H) (A B C : Subgroup G) (Q : Subgroup H)
    (hC : C ≤ f.ker) (hN : f.ker ≤ normalizer (B : Set G))
    (hK : (f.ker : Set G) ⊆ (B ⊓ f.ker : Set G) * (A ⊓ f.ker : Set G) * (C : Set G))
    (hQ : (Q : Set H) = (A.map f : Set H) * (B.map f : Set H)) :
    (Q.comap f : Set G) = (A : Set G) * (B : Set G) * (C : Set G) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : f x ∈ (A.map f : Set H) * (B.map f : Set H) := hQ ▸ hx
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := hx'
    change f a * f b = f x at hab
    have hk : (a * b)⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hab, inv_mul_cancel]
    obtain ⟨_, ⟨b₀, hb₀, a₀, ha₀, rfl⟩, c, hc, hprod⟩ := hK hk
    change (b₀ * a₀) * c = (a * b)⁻¹ * x at hprod
    have hn := hN ha₀.2
    have hmid : a₀⁻¹ * (b * b₀) * a₀ ∈ B :=
      (mem_normalizer_iff''.mp hn (b * b₀)).mp (B.mul_mem hb hb₀.1)
    refine ⟨_, ⟨a * a₀, A.mul_mem ha ha₀.1, _, hmid, rfl⟩, c, hc, ?_⟩
    calc
      _ = a * b * ((b₀ * a₀) * c) := by group
      _ = a * b * ((a * b)⁻¹ * x) := by rw [hprod]
      _ = x := by group
  · rintro x ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    change f ((a * b) * c) ∈ Q
    rw [map_mul, (MonoidHom.mem_ker.mp (hC hc)), mul_one, map_mul]
    rw [← SetLike.mem_coe, hQ]
    exact Set.mul_mem_mul (mem_map_of_mem f ha) (mem_map_of_mem f hb)
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem sup_eq_comap_threeFactor (f : G →* H) (A B C : Subgroup G) (Q : Subgroup H)
    (hC : C ≤ f.ker) (hN : f.ker ≤ normalizer (B : Set G))
    (hK : (f.ker : Set G) ⊆ (B ⊓ f.ker : Set G) * (A ⊓ f.ker : Set G) * (C : Set G))
    (hQ : (Q : Set H) = (A.map f : Set H) * (B.map f : Set H)) :
    A ⊔ B ⊔ C = Q.comap f := by
  have he := comap_eq_threeFactor f A B C Q hC hN hK hQ
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      rw [← SetLike.mem_coe, he]
      simpa using Set.mul_mem_mul (Set.mul_mem_mul ha B.one_mem) C.one_mem
    · intro b hb
      rw [← SetLike.mem_coe, he]
      simpa using Set.mul_mem_mul (Set.mul_mem_mul A.one_mem hb) C.one_mem
    · intro c hc
      rw [← SetLike.mem_coe, he]
      simpa using Set.mul_mem_mul (Set.mul_mem_mul A.one_mem B.one_mem) hc
  · intro x hx
    rw [← SetLike.mem_coe, he] at hx
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx
    exact (A ⊔ B ⊔ C).mul_mem
      ((A ⊔ B ⊔ C).mul_mem ((show A ≤ A ⊔ B ⊔ C from le_sup_left.trans le_sup_left) ha)
        ((show B ≤ A ⊔ B ⊔ C from le_sup_right.trans le_sup_left) hb))
      ((show C ≤ A ⊔ B ⊔ C from le_sup_right) hc)
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] {p : ℕ}

/-- Restrict a lifted Sylow to an actual ambient overgroup of its carrier. -/
theorem exists_sylow_in_of_comap (I J S : Subgroup G) (hJI : J ≤ I) (hSJ : S ≤ J)
    (f : I →* H) (Q : Sylow p H) (hk : IsPGroup p f.ker)
    (hS : S.subgroupOf I = (Q : Subgroup H).comap f)
    (hQ : (S.subgroupOf I).map f = (Q : Subgroup H)) :
    ∃ P : Sylow p J, (P : Subgroup J).map J.subtype = S := by
  let j := inclusion hJI
  let fj := f.comp j
  have hkj : IsPGroup p fj.ker :=
    hk.comap_of_injective j (inclusion_injective hJI)
  have hr : (Q : Subgroup H) ≤ fj.range := by
    intro y hy
    rw [← hQ] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨⟨x,hSJ hx⟩, rfl⟩
  let P := Q.comapOfKerIsPGroup fj hkj hr
  refine ⟨P, ?_⟩
  have he : (P : Subgroup J) = S.subgroupOf J := by
    ext x
    change f (j x) ∈ (Q : Subgroup H) ↔ (x : G) ∈ S
    exact (show j x ∈ (Q : Subgroup H).comap f ↔ j x ∈ S.subgroupOf I from
      Iff.of_eq (congrArg (fun K : Subgroup I => j x ∈ K) hS.symm))
  rw [he, map_subgroupOf_eq_of_le hSJ]
end Subgroup
