module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearLayerDecomposition

/-!
# Restricting the whole deleted module to literal invariant subgroups

A subgroup of R₂(LT) normalized by L defines a subrepresentation of the
marked quotient action. The equivalence with that subrepresentation retains
both original inclusions into G, so finite-copy coordinates give the exact
conjugation model on the subgroup. This applies to the original [W,L],
without choosing an invariant constituent in W.

Source: Aschbacher--Smith 5.1.13(3), printed p.638.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter12.Section02 Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L U : Subgroup G}

/-- An invariant subgroup of the whole reduced group is an actual subrepresentation. -/
@[expose] def moduleSubrepresentation
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLU : L ≤ normalizer (U : Set G)) :
    Subrepresentation (wholeMarkedAction hTL e) where
  toSubmodule := AddSubgroup.toZModSubmodule 2
    (U.comap (((L ⊔ (T : Subgroup G)).subtype).comp (ReducedModule (L ⊔ (T : Subgroup G))).subtype)).toAddSubgroup
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    dsimp only [Function.comp_apply]
    rw [wholeMarkedAction_mk]
    change (l : G) * (v.toMul.val : G) * (l : G)⁻¹ ∈ U
    exact (mem_normalizer_iff.mp (hLU l.property) _).mp hv

/-- Both inclusions are retained in the equivalence with the actual subgroup. -/
@[expose] def moduleSubrepresentationEquiv
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLU : L ≤ normalizer (U : Set G)) (hU : U ≤ wholeReduced T L) :
    Multiplicative (moduleSubrepresentation hTL e hLU).toSubmodule ≃* U := by
  let f : Multiplicative (moduleSubrepresentation hTL e hLU).toSubmodule →* U := {
    toFun v := ⟨(v.toAdd.val.toMul.val : G),v.toAdd.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact MulEquiv.ofBijective f ⟨by
    intro x y he
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) he, by
    intro u
    obtain ⟨r,hr,he⟩ := hU u.property
    change (r : G) = (u : G) at he
    refine ⟨Multiplicative.ofAdd ⟨Additive.ofMul ⟨r,hr⟩,?_⟩,?_⟩
    · change (r : G) ∈ U
      rw [he]
      exact u.property
    · exact Subtype.ext he⟩

/-- The coordinate restriction keeps the actual ambient inclusion. -/
@[simp] theorem moduleSubrepresentationEquiv_apply
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLU : L ≤ normalizer (U : Set G)) (hU : U ≤ wholeReduced T L)
    (v : Multiplicative (moduleSubrepresentation hTL e hLU).toSubmodule) :
    (moduleSubrepresentationEquiv hTL e hLU hU v : G) = (v.toAdd.val.toMul.val : G) := rfl

/-- Coordinates on the subrepresentation give the original conjugation action. -/
theorem subgroup_model_of_coordinates
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLU : L ≤ normalizer (U : Set G)) (hU : U ≤ wholeReduced T L)
    {m : ℕ} (c : (moduleSubrepresentation hTL e hLU).toSubmodule ≃ₗ[ZMod 2]
      (Fin m → BinaryPermutation.natural (Fin 5)))
    (hc : ∀ g v, c ((moduleSubrepresentation hTL e hLU).toRepresentation g v) =
      a5Copies m g (c v)) : IsConjugationModel L U (a5Copies m) := by
  let b := moduleSubrepresentationEquiv hTL e hLU hU
  let f := b.symm.trans c.toAddEquiv.toMultiplicative
  refine ⟨e,f,?_⟩
  intro l v
  let v' := (b.symm v).toAdd
  have hv : (v'.val.toMul.val : G) = (v : G) :=
    congrArg Subtype.val (b.apply_symm_apply v)
  change (b (Multiplicative.ofAdd (c.symm
    (a5Copies m (e (QuotientGroup.mk' (pCore 2 L) l)) (c v')))) : G) = _
  rw [←hc,c.symm_apply_apply]
  change (wholeMarkedAction hTL e (e (QuotientGroup.mk' (pCore 2 L) l)) v'.val).toMul.val.val = _
  rw [wholeMarkedAction_mk]
  change (l : G) * (v'.val.toMul.val : G) * (l : G)⁻¹ = _
  rw [hv]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
