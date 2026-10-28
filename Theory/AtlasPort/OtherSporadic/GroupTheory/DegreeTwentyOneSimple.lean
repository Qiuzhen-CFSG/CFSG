/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/DegreeTwentyOneSimple.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.SimpleStabilizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SylowSevenKernel

/-!
# DegreeTwentyOneSimple

Local stabilizer data yield simplicity for the degree-twenty-one action.
Normal-subgroup alternatives and Sylow-seven restrictions exclude the proper case.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/DegreeTwentyOneSimple.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

theorem simple_degree_twenty_one {G X : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [IsMultiplyPretransitive G X 2]
    (x : X) (hx : Nat.card X = 21) (hG : Nat.card G = 20160)
    (U : Subgroup (stabilizer G x)) (hu : Nat.card U = 16)
    (normal_forms : ∀ W : Subgroup (stabilizer G x), W.Normal → W = ⊥ ∨ W = U ∨ W = ⊤)
    (no_eight : ∀ ρ : stabilizer G x →* Equiv.Perm (Fin 8), ¬ Function.Injective ρ) :
    IsSimpleGroup G := by
  classical
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : IsPreprimitive G X := isPreprimitive_of_is_two_pretransitive inferInstance
  constructor
  intro N hnormal
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  have : IsPretransitive N X := normal_pretransitive N hN
  let T := stabilizer G x
  rcases normal_forms (N.subgroupOf T) inferInstance with hb | hU | ht
  · exfalso
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply regular_normal_impossible N x _ 3 7 (by decide) (by rw [hx]; decide) (by rw [hx]; decide)
    intro n hn
    have hm : (⟨n.val,hn⟩ : T) ∈ N.subgroupOf T := n.prop
    rw [hb,Subgroup.mem_bot] at hm
    exact Subtype.ext (congrArg (fun t : T => t.val) hm)
  · exfalso
    have he : stabilizer N x ≃ N.subgroupOf T := {
      toFun := fun n => ⟨⟨n.val.val,n.prop⟩,n.val.prop⟩
      invFun := fun n => ⟨⟨n.val.val,n.prop⟩,n.val.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have horbit : orbit N x ≃ X := Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
      intro y
      exact ⟨⟨y,mem_orbit_iff.mpr (exists_smul_eq N x y)⟩,rfl⟩⟩
    have hc := Nat.card_congr (orbitProdStabilizerEquivGroup N x)
    rw [Nat.card_prod,Nat.card_congr horbit,Nat.card_congr he,hU,hx,hu] at hc
    have hn : Nat.card N = 336 := hc.symm
    have hs := normal_336_has_eight_sylow x hx N hn
    let := Fintype.ofFinite (Sylow 7 N)
    let e : Sylow 7 N ≃ Fin 8 := Fintype.equivFinOfCardEq (by rwa [Nat.card_eq_fintype_card] at hs)
    let ρ : T →* Equiv.Perm (Fin 8) := e.permCongrHom.toMonoidHom.comp
      ((normalSylowSevenPermutation N).comp T.subtype)
    apply no_eight ρ
    exact e.permCongrHom.injective.comp
      ((normalSylowSevenPermutation_injective x hx hG N hn).comp Subtype.val_injective)
  · right
    apply top_unique
    intro g _
    obtain ⟨n,hn⟩ := exists_smul_eq N x (g • x)
    have hk : n.val⁻¹*g ∈ T := by
      change (n.val⁻¹*g) • x = x
      rw [mul_smul,← hn]
      exact inv_smul_smul n.val x
    have hnk : n.val⁻¹*g ∈ N := by
      have hm : (⟨n.val⁻¹*g,hk⟩ : T) ∈ N.subgroupOf T := by rw [ht]; trivial
      exact hm
    simpa using N.mul_mem n.prop hnk

end Atlas.GroupTheory
