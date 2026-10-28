module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Automorphisms
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Theory.ElementaryAbelian.Injective

/-!
# Complement stabilizers and marked transport for the natural A₆ block

An automorphism preserving the chosen complement is exactly a coordinate
permutation. Transport through a marked split isomorphism identifies the
pointwise fixer of the original sixteen-group with the deleted module and
identifies the full automorphism group with its split extension by S₆.

Source: Aschbacher–Smith 14.3.19(9–10).
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
open scoped Pointwise

noncomputable def complement : Subgroup Model := (inr : Actor →* Model).range

public theorem mem_complement_iff (x : Model) : x∈complement ↔ x.left=1 := by
  constructor
  · rintro ⟨g,rfl⟩
    rfl
  · intro hx
    exact ⟨x.right,SemidirectProduct.ext hx.symm rfl⟩

public theorem diagonal_complement (s : Equiv.Perm (Fin 6)) (g : Actor) :
    diagonal s (inr g)∈complement := by
  rw [mem_complement_iff]
  change naturalMulAction (Fin 6) s 1=1
  exact map_one _

public theorem pointwiseKernel_eq_one_of_preserves_complement
    (k : pointwiseKernel) (hk : ∀g:Actor,k.val (inr g)∈complement) : k=1 := by
  have hi : ∀g:Actor,k.val (inr g)=inr g := by
    intro g
    apply SemidirectProduct.ext
    · exact (mem_complement_iff _).mp (hk g)
    · exact Representation.OneCohomology.splitPointwiseKernel_right action action_injective k _
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  calc
    k.val x = k.val (inl x.left * inr x.right) := congrArg k.val (inl_left_mul_inr_right x).symm
    _ = inl x.left * inr x.right := by rw [map_mul,k.property,hi]
    _ = x := inl_left_mul_inr_right x

public theorem preserves_complement_iff_mem_diagonal
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)
    (a : MulAut Model) :
    (∀g:Actor,a (inr g)∈complement) ↔ a∈diagonal.range := by
  constructor
  · intro ha
    obtain ⟨k,s,rfl⟩ := exists_kernel_mul_diagonal hN a
    have hk : k=1 := pointwiseKernel_eq_one_of_preserves_complement k (by
      intro g
      have he : diagonal s (inr ((MulAut.conjNormal s).symm g))=inr g := by
        apply SemidirectProduct.ext
        · exact map_one _
        · exact MulEquiv.apply_symm_apply _ _
      have h := ha ((MulAut.conjNormal s).symm g)
      change k.val (diagonal s (inr _))∈complement at h
      rwa [he] at h)
    exact ⟨s,by simp [hk]⟩
  · rintro ⟨s,rfl⟩
    exact diagonal_complement s

public theorem complement_stabilizer_eq_diagonal
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    MulAction.stabilizer (MulAut Model) (complement : Set Model)=diagonal.range := by
  ext a
  rw [MulAction.mem_stabilizer_iff]
  change a '' (complement : Set Model) = (complement : Set Model) ↔ a∈diagonal.range
  constructor
  · intro ha
    apply (preserves_complement_iff_mem_diagonal hN a).mp
    intro g
    change a (inr g)∈(complement : Set Model)
    rw [←ha]
    exact ⟨inr g,⟨g,rfl⟩,rfl⟩
  · rintro ⟨s,rfl⟩
    ext x
    constructor
    · rintro ⟨y,⟨g,rfl⟩,rfl⟩
      exact diagonal_complement s g
    · rintro ⟨g,rfl⟩
      refine ⟨inr ((MulAut.conjNormal s).symm g),⟨_,rfl⟩,?_⟩
      apply SemidirectProduct.ext
      · exact map_one _
      · exact MulEquiv.apply_symm_apply _ _

noncomputable def complementStabilizerEquiv
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    MulAction.stabilizer (MulAut Model) (complement : Set Model) ≃* Equiv.Perm (Fin 6) :=
  (MulEquiv.subgroupCongr (complement_stabilizer_eq_diagonal hN)).trans
    (MonoidHom.ofInjective diagonal_injective).symm

variable {K : Type*} [Group K] (A : Subgroup K) (e : K ≃* Model)

public theorem fixingSubgroup_map (hA : A.map e.toMonoidHom=translations) :
    (fixingSubgroup (MulAut K) (A : Set K)).map (MulAut.congr e).toMonoidHom =
      pointwiseKernel := by
  ext a
  rw [mem_map_equiv,mem_fixingSubgroup_iff]
  change (∀x∈A, ((MulAut.congr e).symm a) x=x) ↔ ∀v:Vector,a (inl v)=inl v
  constructor
  · intro ha v
    have hx : e.symm (inl v)∈A := by
      have hm : inl v∈A.map e.toMonoidHom := by rw [hA]; exact ⟨v,rfl⟩
      exact mem_map_equiv.mp hm
    have hh := congrArg e (ha _ hx)
    simpa using hh
  · intro ha x hx
    have hm : e x∈translations := by rw [←hA]; exact mem_map.mpr ⟨x,hx,rfl⟩
    obtain ⟨v,hv⟩ := hm
    apply e.injective
    change e (e.symm (a (e x)))=e x
    rw [MulEquiv.apply_symm_apply,←hv,ha]

noncomputable def markedKernelEquiv (hA : A.map e.toMonoidHom=translations) :
    fixingSubgroup (MulAut K) (A : Set K) ≃* Multiplicative (Deleted (Fin 6)) :=
  ((MulAut.congr e).subgroupMap _).trans
    ((MulEquiv.subgroupCongr (fixingSubgroup_map A e hA)).trans kernelEquiv.symm)

public theorem markedKernel_card (hA : A.map e.toMonoidHom=translations) :
    Nat.card (fixingSubgroup (MulAut K) (A : Set K))=32 := by
  rw [Nat.card_congr (((MulAut.congr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map A e hA))).toEquiv]
  exact pointwiseKernel_card

public theorem markedKernel_elementary (hA : A.map e.toMonoidHom=translations) :
    IsElementaryAbelian 2 (fixingSubgroup (MulAut K) (A : Set K)) := by
  let q := ((MulAut.congr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map A e hA))
  exact IsElementaryAbelian.of_injective q.toMonoidHom q.injective

noncomputable def markedAutomorphismEquiv
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    MulAut K ≃* AutomorphismModel := (MulAut.congr e).trans (automorphismEquiv hN)

end BinaryPermutation.SixNaturalSplit
