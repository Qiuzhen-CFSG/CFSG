module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.OrbitBound
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.SylowBasis
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Normalizer
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.ElementaryAbelian.Injective

/-!
# Strict offender ratio for the deleted A₅ tensor square

Every nontrivial elementary subgroup of S₅ wr C₂ has fixed codimension
strictly greater than twice its rank on the sixteen-dimensional deleted
square. The Sylow permutation basis and Burnside count prove the estimate;
conjugacy gives the full wreath statement. The normalizer theorem transfers
it to the full faithful actor of a normal marked A₅ product.

This excludes the deleted-square alternative in Aschbacher--Smith D.3.7,
printed pp.197–199. No natural-module hypothesis enters this branch.
-/

public section
namespace BinaryPermutation.FiveTensorSquare
open Representation.BinaryOffender

namespace Small

theorem ratio_gt_two (A : Subgroup P) (hA : IsElementaryTwo A) :
    2*rank A < fixedCodim (tensorWreathAction.comp embed) A := by
  have ho := orbit_strict A hA
  have hd := fixedCodim_add_finrank (tensorWreathAction.comp embed) A
  rw [fixedSpace_finrank,finrank_V] at hd
  omega

end Small

/-- Every nontrivial elementary subgroup has strict ratio greater than two. -/
theorem elementary_ratio_gt_two {A : Subgroup Wreath} (hA : IsElementaryTwo A) :
    2*rank A < fixedCodim tensorWreathAction A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Wreath S Small.sylow
  have he : (S:Subgroup Wreath).map (MulAut.conj g).toMonoidHom=Small.embed.range :=
    congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : IsElementaryTwo B := hA.map_conj g
  have hBR : B≤Small.embed.range := he ▸ Subgroup.map_mono hAS
  let E := B.comap Small.embed
  have hmap : E.map Small.embed=B := Subgroup.map_comap_eq_self hBR
  have hE : IsElementaryTwo E := by
    let _ : IsElementaryAbelian 2 B := hB.2
    exact ⟨fun hz => hB.1 (by rw [←hmap,hz,Subgroup.map_bot]),
      IsElementaryAbelian.comap_of_injective Small.embed Small.embed_injective B⟩
  have hr := Small.ratio_gt_two E hE
  have hc : fixedCodim (tensorWreathAction.comp Small.embed) E=
      fixedCodim tensorWreathAction B := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,hmap]
  rw [hc,←rank_map_injective Small.embed Small.embed_injective,hmap] at hr
  simpa only [B,rank_map_conj,fixedCodim_map_conj] using hr

/-- The strict deleted-square bound for the full faithful actor normalizing the marked A₅ product. -/
theorem faithful_actor_ratio_gt_two {H U : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : Alt × Alt →* H) [i.range.Normal]
    (e : Representation.Equiv (ρ.comp i) deletedAction)
    {A : Subgroup H} (hA : IsElementaryTwo A) :
    2*rank A < fixedCodim ρ A := by
  obtain ⟨q,hq,⟨E⟩⟩ := faithful_actor_embedding ρ hρ i e
  let _ : IsElementaryAbelian 2 A := hA.2
  have hmap : IsElementaryTwo (A.map q) :=
    ⟨fun hz => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hq).mp hz),
      IsElementaryAbelian.map q⟩
  have h := elementary_ratio_gt_two hmap
  rw [rank_map_injective q hq,←fixedCodim_map_equivariant ρ tensorWreathAction q
    E.toLinearEquiv (fun g v => Representation.IntertwiningMap.isIntertwining
      ρ (tensorWreathAction.comp q) E.toIntertwiningMap g v)] at h
  exact h

end BinaryPermutation.FiveTensorSquare
