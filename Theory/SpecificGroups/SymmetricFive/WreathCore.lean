module
public import Theory.SpecificGroups.SymmetricFive.WreathComponents
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.TwoCore
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sylow overgroups with core inside the symmetric-five wreath base

Embed the symmetric-four wreath product by fixing the fifth point in each
coordinate. Its order has the full two-part of the symmetric-five wreath
product, and its two-core lies in the base. Sylow conjugacy gives the same
proper overgroup for any prescribed Sylow subgroup.

This is the model input for the core-normalizer containment in
Aschbacher--Smith 15.2.4, printed p.1106.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.WreathCore
open WreathComponents

private def pointEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 4) (Fin 1)).comp
      (MonoidHom.inl (Equiv.Perm (Fin 4)) (Equiv.Perm (Fin 1))))

private theorem pointEmbedding_injective : Function.Injective pointEmbedding := by
  intro x y h
  exact congrArg Prod.fst (Equiv.Perm.sumCongrHom_injective
    ((Equiv.permCongrHom (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5)).injective h))

private def embedding : SymmetricFourWreath.W →* W where
  toFun x := ⟨fun i => pointEmbedding (x.left i),x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  apply RegularWreathProduct.ext
  · funext i
    exact pointEmbedding_injective (congrArg (fun z : W => z.left i) h)
  · exact congrArg (fun z : W => z.right) h

private theorem model_card : Nat.card W = 28800 := by
  norm_num [W,WreathComponents.Sym,C2,RegularWreathProduct.card,
    Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

private theorem range_card : Nat.card embedding.range = 1152 :=
  (Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv).symm.trans
    SymmetricFourWreath.card_W

private theorem range_proper : embedding.range ≠ ⊤ := by
  intro h
  have hh := range_card
  rw [h,card_top,model_card] at hh
  omega

private theorem range_core : embedding.range.pCoreIn 2 ≤ base := by
  rw [pCoreIn_range_of_injective _ _ embedding_injective,← SymmetricFourWreath.A_eq_twoCore]
  rintro _ ⟨x,hx,rfl⟩
  exact ((SymmetricFourWreath.mem_elementary true true x).mp hx).1

private theorem range_sylow : ∃ P : Sylow 2 W, (P : Subgroup W) ≤ embedding.range := by
  let S := SymmetricFourWreath.standardSylow
  let Q := (S : Subgroup SymmetricFourWreath.W).map embedding
  have hc : Nat.card Q = 128 := by
    rw [card_map_of_injective embedding_injective,SymmetricFourWreath.standardSylow_coe,
      ← Nat.card_congr (MonoidHom.ofInjective SymmetricFourWreath.sylowEmbedding_injective).toEquiv,
      SymmetricFourWreath.card_P]
  refine ⟨Sylow.ofCard Q ?_,(S : Subgroup SymmetricFourWreath.W).map_le_range embedding⟩
  rw [hc,model_card]
  decide +kernel

/-- Each prescribed Sylow lies in a proper subgroup whose two-core lies in the wreath base. -/
theorem exists_sylow_overgroup_core_in_base (P : Sylow 2 W) :
    ∃ B : Subgroup W, (P : Subgroup W) ≤ B ∧ B ≠ ⊤ ∧ B.pCoreIn 2 ≤ base := by
  obtain ⟨S,hS⟩ := range_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W S P
  let a := MulAut.conj g
  refine ⟨embedding.range.map a.toMonoidHom,?_,?_,?_⟩
  · rw [← hg]
    exact map_mono hS
  · intro ht
    apply range_proper
    have hh := congrArg (comap a.toMonoidHom) ht
    simpa only [comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective,comap_top] using hh
  · rw [← map_pCoreIn_of_injective 2 _ a.toMonoidHom a.injective]
    have hb : base.map a.toMonoidHom = base := normal_iff_map_conj_eq.mp inferInstance g
    exact (map_mono range_core).trans_eq hb

end Theory.SpecificGroups.SymmetricFive.WreathCore
