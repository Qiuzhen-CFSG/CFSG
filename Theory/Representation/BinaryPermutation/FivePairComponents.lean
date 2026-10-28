module
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Theory.SpecificGroups.SymmetricFive.WreathComponents

/-!
# Restricting the paired five-point module to an actual component

Every C-component of S₅ wr C₂ is one of its two A₅ factors. Matching the
literal wreath coordinates makes its action natural on one four-space and
trivial on the other. The sum of the twenty three-cycle operators identifies the
natural summand with the whole commutator space.

For a surjective action with kernel O₂(D), subnormal core restriction
identifies the kernel on the actual component K with O₂(K). The resulting
embedded natural module has order sixteen. The source application retains
both original chief sections in Aschbacher--Smith 15.2.4, pp.1105--1107;
the underlying paired representation is the natural row of 15.1.12(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace BinaryPermutation.FivePair
open Theory.SpecificGroups.SymmetricFive.WreathComponents

/-- A component acts on exactly one of the two marked natural summands. -/
theorem component_coordinates {K : Subgroup Wreath} (hK : K.IsCComponent) :
    ∃ (q : K ≃* alternatingGroup (Fin 5))
      (c : (Core × Core) ≃ₗ[ZMod 2] (Core × Core)),
      ∀ g : K, ∀ v, c (wreathRepresentation (g : Wreath) v) =
        (alternatingCoreRepresentation (Fin 5) (q g) (c v).1, (c v).2) := by
  rcases component_eq_factor hK with hk | hk
  · let E := (solvableResidual Sym).prod (⊥ : Subgroup Sym)
    let e : K ≃* E := (MulEquiv.subgroupCongr hk).trans
      (equivMapOfInjective E baseHom baseHom_injective).symm
    let a : E ≃* solvableResidual Sym := {
      toFun x := ⟨x.val.1,x.property.1⟩
      invFun x := ⟨(x,1),x.property,one_mem _⟩
      left_inv x := Subtype.ext (Prod.ext rfl x.property.2.symm)
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    let q := e.trans (a.trans (MulEquiv.subgroupCongr symmetric_residual))
    refine ⟨q,LinearEquiv.refl _ _,?_⟩
    intro g v
    have he : baseHom (e g : Sym × Sym) = (g : Wreath) := by
      exact congrArg Subtype.val ((equivMapOfInjective E baseHom baseHom_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hk) g))
    have hbase : (g : Wreath) = FivePair.base ((q g : Sym),1) := by
      rw [←he]
      have hp : (e g : Sym × Sym) = ((q g : Sym),1) :=
        Prod.ext rfl (e g).property.2
      rw [hp]
      exact baseHom_apply _
    rw [hbase]
    exact wreathToLinear_base _ _
  · let E := (⊥ : Subgroup Sym).prod (solvableResidual Sym)
    let e : K ≃* E := (MulEquiv.subgroupCongr hk).trans
      (equivMapOfInjective E baseHom baseHom_injective).symm
    let a : E ≃* solvableResidual Sym := {
      toFun x := ⟨x.val.2,x.property.2⟩
      invFun x := ⟨(1,x),one_mem _,x.property⟩
      left_inv x := Subtype.ext (Prod.ext x.property.1.symm rfl)
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    let q := e.trans (a.trans (MulEquiv.subgroupCongr symmetric_residual))
    refine ⟨q,LinearEquiv.prodComm _ _ _,?_⟩
    intro g v
    have he : baseHom (e g : Sym × Sym) = (g : Wreath) := by
      exact congrArg Subtype.val ((equivMapOfInjective E baseHom baseHom_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hk) g))
    have hbase : (g : Wreath) = FivePair.base (1,(q g : Sym)) := by
      rw [←he]
      have hp : (e g : Sym × Sym) = (1,(q g : Sym)) :=
        Prod.ext (e g).property.1 rfl
      rw [hp]
      exact baseHom_apply _
    rw [hbase]
    change (wreathToLinear (FivePair.base (1,(q g : Sym))) v).swap = _
    rw [wreathToLinear_base,FivePair.action_apply]
    simp only [map_one,Module.End.one_apply,LinearEquiv.prodComm_apply]
    rfl

end BinaryPermutation.FivePair


namespace BinaryPermutation.FivePair

/-- Restrict the literal action map and retain the intrinsic component kernel. -/
theorem restricted_component_coordinates
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : D →* Wreath) (hf : Function.Surjective f) (hk : f.ker = pCore 2 D)
    (e : V ≃ₗ[ZMod 2] (Core × Core))
    (he : ∀ g v, e (ρ g v) = wreathRepresentation (f g) (e v))
    (K : Subgroup D) (hK : K.IsCComponent) :
    ∃ (q : K →* alternatingGroup (Fin 5))
      (c : V ≃ₗ[ZMod 2] (Core × Core)),
      Function.Surjective q ∧ q.ker = pCore 2 K ∧
      ∀ g : K, ∀ v, c (ρ (g : D) v) =
        (alternatingCoreRepresentation (Fin 5) (q g) (c v).1, (c v).2) := by
  let : Group.IsSolvable f.ker := by
    rw [hk]
    let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent (p := 2)
    infer_instance
  obtain ⟨a,b,hab⟩ := component_coordinates (cComponent_map_of_solvable_ker hK f hf)
  let q := a.toMonoidHom.comp (f.subgroupMap K)
  refine ⟨q,e.trans b,
    a.surjective.comp (f.subgroupMap_surjective K),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ a.injective,Subgroup.ker_subgroupMap,
      hk,pCore_subnormal_eq_comap 2 hK.subnormal]
    rfl
  · intro g v
    change b (e (ρ g v)) = _
    rw [he]
    exact hab (f.subgroupMap K g) (e v)

/-- The natural summand is precisely the full commutator space. -/
theorem moved_embedding_of_component_coordinates
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (q : D →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : V ≃ₗ[ZMod 2] (Core × Core))
    (ha : ∀ g v, c (ρ g v) =
      (alternatingCoreRepresentation (Fin 5) (q g) (c v).1, (c v).2)) :
    ∃ j : Core →ₗ[ZMod 2] V, Function.Injective j ∧
      (∀ g v, j (alternatingCoreRepresentation (Fin 5) (q g) v) = ρ g (j v)) ∧
      j.range = subspaceCommutator ρ ⊤ ⊤ := by
  let j : Core →ₗ[ZMod 2] V := c.symm.toLinearMap.comp (LinearMap.inl _ _ _)
  have hj (v : Core) : c (j v) = (v,0) := c.apply_symm_apply _
  have hinj : Function.Injective j := by
    intro v w he
    exact congrArg Prod.fst ((hj v).symm.trans ((congrArg c he).trans (hj w)))
  have he (g : D) (v : Core) :
      j (alternatingCoreRepresentation (Fin 5) (q g) v) = ρ g (j v) := by
    apply c.injective
    rw [hj,ha,hj]
  refine ⟨j,hinj,he,?_⟩
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    have hz : 20 • j v = 0 := by
      rw [←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
      change (20 : ZMod 2) • j v = 0
      rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
    have hs : (∑ g ∈ FiveCentralExtension.cubes,
        (j (coreRepresentation (Fin 5) g v) - j v)) = j v := by
      rw [Finset.sum_sub_distrib,Finset.sum_const,FiveCentralExtension.cubes_card,hz,
        sub_zero,←map_sum,FiveCentralExtension.core_sum]
    rw [←hs]
    apply Submodule.sum_mem
    intro g hg
    obtain ⟨a,haq⟩ := hq ⟨g,FiveCentralExtension.cubes_even g hg⟩
    have hh := he a v
    rw [haq] at hh
    change j (coreRepresentation (Fin 5) g v) = ρ a (j v) at hh
    rw [hh]
    exact Submodule.subset_span ⟨a,mem_top _,j v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    refine ⟨alternatingCoreRepresentation (Fin 5) (q g) (c v).1 - (c v).1,?_⟩
    apply c.injective
    rw [hj,map_sub,ha]
    ext <;> simp

end BinaryPermutation.FivePair

namespace BinaryPermutation.FivePair

/-- The actual component has a natural moved four-space with kernel O₂(K). -/
theorem restricted_component_moved
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : D →* Wreath) (hf : Function.Surjective f) (hk : f.ker = pCore 2 D)
    (e : V ≃ₗ[ZMod 2] (Core × Core))
    (he : ∀ g v, e (ρ g v) = wreathRepresentation (f g) (e v))
    (K : Subgroup D) (hK : K.IsCComponent) :
    ∃ (q : K →* alternatingGroup (Fin 5)) (j : Core →ₗ[ZMod 2] V),
      Function.Surjective q ∧ q.ker = pCore 2 K ∧ Function.Injective j ∧
      (∀ g v, j (alternatingCoreRepresentation (Fin 5) (q g) v) = ρ (g : D) (j v)) ∧
      j.range = subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ ∧
      Nat.card (subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤) = 16 := by
  obtain ⟨q,c,hq,hker,ha⟩ := restricted_component_coordinates ρ f hf hk e he K hK
  obtain ⟨j,hj,hact,hr⟩ := moved_embedding_of_component_coordinates (ρ.comp K.subtype) q hq c ha
  refine ⟨q,j,hq,hker,hj,hact,hr,?_⟩
  rw [←hr,←Nat.card_congr (LinearEquiv.ofInjective j hj).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod 2),BinaryPermutation.finrank_core]
  norm_num

end BinaryPermutation.FivePair
