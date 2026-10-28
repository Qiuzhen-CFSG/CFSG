module
public import Theory.Representation.BinaryOffender.PerfectMoved
/-!
# Central projections preserve the moved section

For a perfect actor, a surjective equivariant linear map with pointwise fixed
kernel induces an equivalence between the moved submodules modulo their fixed
vectors. A quotient-fixed vector lifts to a fixed vector by perfectness, so
no splitting of the central extension is required.

The original 13.7.18 application projects U_H/V₁ onto U_H/U₀ and retains the
marked B.5 component section.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_movedCentralQuotientEquiv_of_central_surjection
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (K : Subgroup G) [Group.IsPerfect K]
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ v, f (ρ k v) = σ k (f v))
    (hk : f.ker ≤ fixedSpace ρ K) :
    ∃ (hm : ∀ v : subspaceCommutator ρ ⊤ K,
        f v ∈ subspaceCommutator σ ⊤ K)
      (e : (subspaceCommutator ρ ⊤ K ⧸
          (fixedSpace ρ K).comap (subspaceCommutator ρ ⊤ K).subtype) ≃ₗ[ZMod 2]
        (subspaceCommutator σ ⊤ K ⧸
          (fixedSpace σ K).comap (subspaceCommutator σ ⊤ K).subtype)),
      ∀ v, e (Submodule.Quotient.mk v) = Submodule.Quotient.mk ⟨f v,hm v⟩ := by
  classical
  let I := subspaceCommutator ρ ⊤ K
  let J := subspaceCommutator σ ⊤ K
  have hmap : I.map f = J := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,v,_,rfl⟩
      change f (ρ k v-v) ∈ J
      rw [map_sub,he ⟨k,hk⟩]
      exact Submodule.subset_span ⟨k,hk,f v,Submodule.mem_top,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,w,_,rfl⟩
      obtain ⟨v,rfl⟩ := hf w
      refine ⟨ρ k v-v,Submodule.subset_span ⟨k,hk,v,Submodule.mem_top,rfl⟩,?_⟩
      rw [map_sub,he ⟨k,hk⟩]
  have hm (v : I) : f v ∈ J := hmap ▸ Submodule.mem_map_of_mem v.property
  let g : I →ₗ[ZMod 2] J := (f.comp I.subtype).codRestrict J hm
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨v,hv,heq⟩ := (show (w : W) ∈ I.map f from hmap.symm ▸ w.property)
    exact ⟨⟨v,hv⟩,Subtype.ext heq⟩
  let F := (fixedSpace σ K).comap f
  have hF : K ≤ subspaceStabilizer ρ F := by
    apply le_subspaceStabilizer
    intro k hk v hv
    change f (ρ k v) ∈ fixedSpace σ K
    change ∀ k : K, σ k (f v) = f v at hv
    rw [he ⟨k,hk⟩,hv ⟨k,hk⟩]
    exact hv
  have hCF : subspaceCommutator ρ F K ≤ fixedSpace ρ K := by
    apply le_trans (b := f.ker) ?_ hk
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,hv,rfl⟩
    change f (ρ k v-v)=0
    change ∀ k : K, σ k (f v) = f v at hv
    rw [map_sub,he ⟨k,hk⟩,hv ⟨k,hk⟩,sub_self]
  have hFl : F ≤ fixedSpace ρ K :=
    le_fixedSpace_of_commutator_le_fixedSpace ρ K F hF hCF
  have hfix (v : I) : v.val ∈ fixedSpace ρ K ↔ f v ∈ fixedSpace σ K := by
    constructor
    · intro hv k
      change σ k (f v) = f v
      change ∀ k : K, ρ k v.val = v.val at hv
      rw [←he k,hv k]
    · exact fun hv => hFl hv
  let P := (fixedSpace ρ K).comap I.subtype
  let Q := (fixedSpace σ K).comap J.subtype
  let q : I →ₗ[ZMod 2] (J ⧸ Q) := Q.mkQ.comp g
  have hqker : q.ker = P := by
    ext v
    change Submodule.Quotient.mk (g v) = 0 ↔ v.val ∈ fixedSpace ρ K
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hfix v).symm
  let l : (I ⧸ P) →ₗ[ZMod 2] (J ⧸ Q) := P.liftQ q hqker.ge
  have hl : Function.Bijective l := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      exact Submodule.ker_liftQ_eq_bot P q hqker.ge hqker.le
    · intro w
      obtain ⟨j,rfl⟩ := Q.mkQ_surjective w
      obtain ⟨v,rfl⟩ := hg j
      exact ⟨Submodule.Quotient.mk v,rfl⟩
  exact ⟨hm,LinearEquiv.ofBijective l hl,fun _ => rfl⟩
end Representation.BinaryOffender
