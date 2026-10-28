module
public import Theory.Representation.BinaryOffender.NormalizerNonStrong
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# Section costs with the original component-action kernel

A faithful marked normal section detects its component's conjugation image,
even when the whole elementary actor has a nontrivial kernel on that component.
Kernel inclusion bounds the image rank by the actual section-action rank.
Non-strong and non-FF model bounds then give weak and strict section costs.
Two images that jointly detect the actor give an additive bound on its rank.

These are the kernel-preserving inputs for the two-factor Hermitian exclusion
in Aschbacher--Smith D.3.7, printed p.199.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G K V W : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem marked_normal_action_kernel_le
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (μ : Representation (ZMod 2) K W) (hμ : Function.Injective μ)
    (q : N →* K) (hq : Function.Surjective q) (α : G →* MulAut K)
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (b : Representation.Equiv (ρ.comp N.subtype) (μ.comp q)) :
    (actionHom ρ).ker ≤ α.ker := by
  intro a ha
  have hr : ρ a = 1 := congrArg (imageRepresentation ρ) ha
  have hrinv : ρ a⁻¹ = 1 := by
    have hh := ρ.map_mul a a⁻¹
    rw [mul_inv_cancel,map_one,hr,one_mul] at hh
    exact hh.symm
  have he (k : N) : μ (q (MulAut.conjNormal a k)) = μ (q k) := by
    have hc : ρ ((MulAut.conjNormal a k : N) : G) = ρ (k : G) := by
      change ρ (a * (k : G) * a⁻¹) = _
      simp only [map_mul,hr,hrinv,one_mul,mul_one]
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := b.toLinearEquiv.surjective v
    have hl := LinearMap.congr_fun (b.isIntertwining' (MulAut.conjNormal a k)) w
    have hk := LinearMap.congr_fun (b.isIntertwining' k) w
    exact hl.symm.trans ((congrArg b.toLinearEquiv (LinearMap.congr_fun hc w)).trans hk)
  apply DFunLike.ext
  intro g
  obtain ⟨k,rfl⟩ := hq g
  exact (hα a k).symm.trans (hμ (he k))

variable [Finite G]

theorem rank_image_le_actionSubgroup
    {J : Type*} [Group J] (ρ : Representation (ZMod 2) G V)
    (α : G →* J) (hk : (actionHom ρ).ker ≤ α.ker) (A : Subgroup G) :
    rank (A.map α) ≤ rank (actionSubgroup ρ A) := by
  let f := (actionHom ρ).comp A.subtype
  let g := α.comp A.subtype
  have hk' : f.ker ≤ g.ker := fun a ha => hk ha
  have hi : g.ker.index ≤ f.ker.index := Subgroup.index_antitone hk'
  rw [Subgroup.index_ker,Subgroup.index_ker] at hi
  have hf : f.range = actionSubgroup ρ A := actionHom_subgroup_range ρ A
  have hg : g.range = A.map α := by rw [MonoidHom.range_comp,range_subtype]
  rw [hf,hg] at hi
  exact Nat.log_mono_right hi

theorem image_rank_le_fixedCodim_of_nonStrong
    {J : Type*} [Group J] (ρ : Representation (ZMod 2) G V)
    (α : G →* J) (hk : (actionHom ρ).ker ≤ α.ker)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hn : ¬ IsStrongFFModule (imageRepresentation ρ)) :
    rank (A.map α) ≤ fixedCodim ρ A := by
  have hr := rank_image_le_actionSubgroup ρ α hk A
  let : IsElementaryAbelian 2 (actionSubgroup ρ A) := IsElementaryAbelian.map _
  by_cases hb : actionSubgroup ρ A = ⊥
  · rw [hb,rank_bot] at hr
    omega
  · have hb' : rank (actionSubgroup ρ A) ≤ fixedCodim ρ A := by
      by_contra! h
      exact hn ⟨actionSubgroup ρ A,⟨hb,inferInstance⟩,by simpa using h⟩
    exact hr.trans hb'

theorem image_rank_lt_fixedCodim_of_nonFF
    {J : Type*} [Group J] (ρ : Representation (ZMod 2) G V)
    (α : G →* J) (hk : (actionHom ρ).ker ≤ α.ker)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hpos : 0 < rank (A.map α))
    (hn : ¬ IsFFModule (imageRepresentation ρ)) :
    rank (A.map α) < fixedCodim ρ A := by
  have hr := rank_image_le_actionSubgroup ρ α hk A
  let : IsElementaryAbelian 2 (actionSubgroup ρ A) := IsElementaryAbelian.map _
  have hb : actionSubgroup ρ A ≠ ⊥ := by
    intro h
    rw [h,rank_bot] at hr
    omega
  have hb' : rank (actionSubgroup ρ A) < fixedCodim ρ A := by
    by_contra! h
    exact hn ⟨actionSubgroup ρ A,⟨hb,inferInstance⟩,by simpa using h⟩
  exact hr.trans_lt hb'

omit [Finite G] in
private theorem elementary_card_pow_rank {X : Type*} [Group X]
    (P : Subgroup X) [Finite P] [IsElementaryAbelian 2 P] : Nat.card P = 2^rank P := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 P).exists_card_eq
  rw [rank,hk,Nat.log_pow (by decide : 1<2)]

/-- Two images that jointly detect the full elementary actor bound its rank additively. -/
theorem rank_le_sum_image_ranks
    {J Q : Type*} [Group J] [Group Q]
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (α : G →* J) (β : G →* Q)
    (hf : Function.Injective ((α.prod β).comp A.subtype)) :
    rank A ≤ rank (A.map α) + rank (A.map β) := by
  let f : A → (A.map α) × (A.map β) := fun a =>
    (⟨α a,mem_map_of_mem α a.property⟩,⟨β a,mem_map_of_mem β a.property⟩)
  have hfi : Function.Injective f := by
    intro a b he
    apply hf
    exact Prod.ext (congrArg (fun x => x.1.val) he) (congrArg (fun x => x.2.val) he)
  let : Finite (A.map α) := Finite.of_surjective (α.subgroupMap A) (α.subgroupMap_surjective A)
  let : Finite (A.map β) := Finite.of_surjective (β.subgroupMap A) (β.subgroupMap_surjective A)
  have hc := Nat.card_le_card_of_injective f hfi
  let : IsElementaryAbelian 2 (A.map α) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map β) := IsElementaryAbelian.map _
  rw [Nat.card_prod,elementary_card_pow_rank A,elementary_card_pow_rank (A.map α),elementary_card_pow_rank (A.map β),←pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
end Representation.BinaryOffender
