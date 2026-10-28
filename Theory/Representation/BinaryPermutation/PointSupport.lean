module
public import Theory.Representation.BinaryPermutation.PointOrbit
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# The moved support of a five-point permutation quotient

For a transitive subgroup, the differences of point vectors span exactly the
augmentation submodule. An equivariant quotient whose kernel is constant
therefore embeds this entire four-dimensional submodule as its commutator
support. The odd degree separates the constant line from augmentation.

The NormalFourModule application uses the original relatively normal component
and the literal image of its group commutator, with the original quotient map.
Source: the permutation-module argument underlying Aschbacher--Smith
14.3.6(1) and 14.6.20, printed pp.991,1037.
-/

public noncomputable section
namespace BinaryPermutation
open Representation Representation.BinaryOffender Subgroup
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- Transitive permutation differences span the whole augmentation submodule. -/
theorem transitive_commutator_eq_core
    (α : H →* Equiv.Perm (Fin 5)) (A : Subgroup H)
    (ht : ∀ i j : Fin 5, ∃ g : A, α g i = j) :
    subspaceCommutator ((representation (Fin 5)).comp α) ⊤ A = core (Fin 5) := by
  let σ := (representation (Fin 5)).comp α
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨g,hg,v,_,rfl⟩
    change augmentation (Fin 5) (representation (Fin 5) (α g) v - v) = 0
    rw [map_sub,augmentation_permute,sub_self]
  · intro v hv
    have hp (j : Fin 5) : (Pi.single j (1 : ZMod 2) - Pi.single 0 1) ∈
        subspaceCommutator σ ⊤ A := by
      obtain ⟨g,hg⟩ := ht 0 j
      have he : σ g (Pi.single 0 1) = Pi.single j 1 := by
        ext k
        change (Pi.single 0 (1 : ZMod 2) : Fin 5 → ZMod 2) ((α g).symm k) =
          (Pi.single j 1 : Fin 5 → ZMod 2) k
        simp only [Pi.single_apply,Equiv.symm_apply_eq,hg]
      rw [←he]
      exact Submodule.subset_span ⟨g,g.property,Pi.single 0 1,Submodule.mem_top,rfl⟩
    have he : v = ∑ j : Fin 5, v j • (Pi.single j 1 - Pi.single 0 1) := by
      rw [Finset.sum_congr rfl (fun j _ => smul_sub (v j) _ _),Finset.sum_sub_distrib,
        ←Finset.sum_smul]
      have hh : ∑ j : Fin 5, v j = 0 := hv
      rw [hh,zero_smul,sub_zero]
      ext k
      simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hp j))

/-- A constant-kernel quotient retains the entire four-dimensional moved support. -/
theorem five_point_support
    (ρ : Representation (ZMod 2) H W) (α : H →* Equiv.Perm (Fin 5))
    (A : Subgroup H) (ht : ∀ i j : Fin 5, ∃ g : A, α g i = j)
    (F : IntertwiningMap ((representation (Fin 5)).comp α) ρ)
    (hF : Function.Surjective F) (hk : F.toLinearMap.ker ≤ constants (Fin 5)) :
    subspaceCommutator ρ ⊤ A = (core (Fin 5)).map F.toLinearMap ∧
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 4 ∧
    Function.Injective (F.toLinearMap.domRestrict (core (Fin 5))) := by
  have hs : subspaceCommutator ρ ⊤ A = (core (Fin 5)).map F.toLinearMap := by
    have hh := subspaceCommutator_map_embedding ρ
      ((representation (Fin 5)).comp α) (MonoidHom.id H) F.toLinearMap
      (fun g v => (IntertwiningMap.isIntertwining _ _ F g v).symm) A ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr hF,Subgroup.map_id,
      transitive_commutator_eq_core α A ht] at hh
    exact hh
  have hinj : Function.Injective (F.toLinearMap.domRestrict (core (Fin 5))) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp (core_isCompl_constants (Fin 5) (by decide)).disjoint)
      v v.property (hk (show F v = 0 from hv))
  have hd := LinearMap.finrank_range_of_inj hinj
  have he : LinearMap.range (F.toLinearMap.domRestrict (core (Fin 5))) =
      (core (Fin 5)).map F.toLinearMap := by
    ext v
    exact ⟨fun ⟨x,hx⟩ => ⟨x,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩
  rw [he] at hd
  refine ⟨hs,?_,hinj⟩
  rw [hs,hd,finrank_core]
  rfl

end BinaryPermutation
