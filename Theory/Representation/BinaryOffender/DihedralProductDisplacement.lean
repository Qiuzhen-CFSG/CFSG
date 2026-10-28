module
public import Theory.Representation.BinaryOffender.DihedralDisplacement
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Displacements in two commuting dihedral factors

For disjoint moved summands with a globally fixed supplement, the ranks of
factor displacements add. Thus an elementary binary subgroup of a product
of two odd dihedral groups, each moving a four-dimensional summand, cannot
have all displacement ranks at most three unless it lies in one factor.

The fixed supplement is essential to the additive rank argument and is
supplied by the original source module in Selection.RankEightConfinement.
This implements the factor-confinement step of Aschbacher--Smith 14.6.13,
printed p.1032, independently of the critical-pair setup.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem fixes_other_moved_of_disjoint (ρ : Representation (ZMod 2) G V)
    (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hd : Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    {a : G} (ha : a ∈ A) {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ B) : ρ a v = v := by
  have hs : ∀ v ∈ subspaceCommutator ρ ⊤ B, ρ a v ∈ subspaceCommutator ρ ⊤ B := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b,hb,w,_,rfl⟩ := hv
      have he : ρ a (ρ b w) = ρ b (ρ a w) := by
        rw [← Module.End.mul_apply,← map_mul,(hc a ha b hb).eq,map_mul,Module.End.mul_apply]
      rw [map_sub,he]
      exact Submodule.subset_span ⟨b,hb,ρ a w,Submodule.mem_top,rfl⟩
    | zero => simp only [map_zero,Submodule.zero_mem]
    | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
    | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv
  have hI : ρ a v - v ∈ subspaceCommutator ρ ⊤ A :=
    Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have hJ : ρ a v - v ∈ subspaceCommutator ρ ⊤ B :=
    (subspaceCommutator ρ ⊤ B).sub_mem (hs v hv) hv
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ hI hJ)

private theorem displacement_range_le_product (ρ : Representation (ZMod 2) G V)
    (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hd : Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    (hs : (subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B) ⊔
      fixedSpace ρ ⊤ = ⊤) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    LinearMap.range (ρ a - LinearMap.id) ≤ LinearMap.range (ρ (a*b) - LinearMap.id) := by
  rintro _ ⟨v,rfl⟩
  obtain ⟨w,hw,c,hc',rfl⟩ := Submodule.mem_sup.mp (hs.ge (Submodule.mem_top (x := v)))
  obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hw
  have haj := fixes_other_moved_of_disjoint ρ A B hc hd ha hj
  have hbi := fixes_other_moved_of_disjoint ρ B A
    (fun b hb a ha => (hc a ha b hb).symm) hd.symm hb hi
  have hac : ρ a c = c := hc' ⟨a,mem_top _⟩
  refine ⟨i,?_⟩
  simp only [LinearMap.sub_apply,LinearMap.id_apply,map_mul,Module.End.mul_apply,
    map_add,hbi,haj,hac]
  abel

/-- A fixed supplement prevents the two disjoint factors from sharing
an additional source for their displacement images. Their ranks therefore add. -/
theorem displacement_rank_product_of_fixed_supplement
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hd : Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    (hs : (subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B) ⊔
      fixedSpace ρ ⊤ = ⊤) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (a*b) - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) +
      Module.finrank (ZMod 2) (LinearMap.range (ρ b - LinearMap.id)) := by
  have hrA : LinearMap.range (ρ a - LinearMap.id) ≤ subspaceCommutator ρ ⊤ A := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have hrB : LinearMap.range (ρ b - LinearMap.id) ≤ subspaceCommutator ρ ⊤ B := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  have he : LinearMap.range (ρ (a*b) - LinearMap.id) =
      LinearMap.range (ρ a - LinearMap.id) ⊔ LinearMap.range (ρ b - LinearMap.id) := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      have hv : ρ b v - v ∈ subspaceCommutator ρ ⊤ B :=
        Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
      have hf := fixes_other_moved_of_disjoint ρ A B hc hd ha hv
      have hh : ρ (a*b) v - v =
          (ρ a v - v) + (ρ b v - v) := by
        simp only [map_sub] at hf
        simp only [map_mul,Module.End.mul_apply]
        calc
          ρ a (ρ b v) - v = (ρ a (ρ b v) - ρ a v) + (ρ a v - v) := by abel
          _ = (ρ b v - v) + (ρ a v - v) := by rw [hf]
          _ = (ρ a v - v) + (ρ b v - v) := add_comm _ _
      change ρ (a*b) v - v ∈ _
      rw [hh]
      exact Submodule.add_mem_sup ⟨v,rfl⟩ ⟨v,rfl⟩
    · apply sup_le
      · exact displacement_range_le_product ρ A B hc hd hs ha hb
      · rw [(hc a ha b hb).eq]
        exact displacement_range_le_product ρ B A
          (fun b hb a ha => (hc a ha b hb).symm) hd.symm
          (by rwa [sup_comm (subspaceCommutator ρ ⊤ B)] ) hb ha
  rw [he]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (ρ a - LinearMap.id)) (LinearMap.range (ρ b - LinearMap.id))
  rwa [(hd.mono hrA hrB).eq_bot,finrank_bot,add_zero] at h

/-- In two commuting dihedral factors with four-dimensional moved summands,
a binary elementary actor whose displacements all have rank at most three
is confined to one factor. -/
theorem dihedral_actor_le_factor_of_displacement_le_three
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (A B C : Subgroup G)
    [IsElementaryAbelian 2 C] (hC : C ≤ A ⊔ B)
    (eA : A ≃* DihedralGroup p) (eB : B ≃* DihedralGroup p)
    (hAB : Disjoint A B) (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hd : Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    (hs : (subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B) ⊔
      fixedSpace ρ ⊤ = ⊤)
    (hA : 4 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A))
    (hB : 4 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ B))
    (hr : ∀ t ∈ C, Module.finrank (ZMod 2)
      (LinearMap.range (ρ t - LinearMap.id)) ≤ 3) : C ≤ A ∨ C ≤ B := by
  apply SubgroupClass.subset_union.mp
  intro t ht
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    A B hAB (fun a ha b hb => (hc a ha b hb).symm)
  obtain ⟨⟨x,y⟩,hxy⟩ := e.surjective ⟨t,hC ht⟩
  have heq : (x:G) * y = t := (he x y).symm.trans (congrArg Subtype.val hxy)
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 C) (⟨t,ht⟩ : C))
  have hxy2 : (x:G)^2 * (y:G)^2 = 1 := by
    rw [← (hc x x.property y y.property).mul_pow,heq,ht2]
  have hh := disjoint_iff_mul_eq_one.mp hAB (A.pow_mem x.property 2)
    (B.pow_mem y.property 2) hxy2
  by_cases hx : x = 1
  · right
    have hy : (y:G) = t := by simpa only [hx,Subgroup.coe_one,one_mul] using heq
    exact hy ▸ y.property
  · by_cases hy : y = 1
    · left
      have hx' : (x:G) = t := by simpa only [hy,Subgroup.coe_one,mul_one] using heq
      exact hx' ▸ x.property
    · have hdx := dihedral_moved_le_twice_displacement ρ hp A eA x hx (Subtype.ext hh.1)
      have hdy := dihedral_moved_le_twice_displacement ρ hp B eB y hy (Subtype.ext hh.2)
      have hsum := displacement_rank_product_of_fixed_supplement ρ A B hc hd hs x.property y.property
      rw [heq] at hsum
      have hrt := hr t ht
      omega

/-- Every elementary binary subgroup of either odd dihedral group has rank
at most one. Nontriviality makes this an equality at the endpoint consumer. -/
theorem elementary_rank_le_one_of_dihedral [Finite G]
    {p : ℕ} (hp : p = 3 ∨ p = 5) (A C : Subgroup G)
    (e : A ≃* DihedralGroup p) [IsElementaryAbelian 2 C] (hle : C ≤ A) : rank C ≤ 1 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
  have hdiv := card_dvd_of_le hle
  rw [hn,Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hdiv
  have hsmall : n ≤ 1 := by
    by_contra! hh
    have hfour : 4 ∣ 2*p := (Nat.pow_dvd_pow 2 hh).trans hdiv
    rcases hp with rfl | rfl <;> norm_num at hfour
  simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hsmall
end Representation.BinaryOffender
