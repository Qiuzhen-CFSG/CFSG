module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.SourceAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags

/-!
# A deleted flag in the basis of the actual source Sylow subgroup

The index-three recognition theorem constructs an actual partial flag.
Choose full-flag coordinates for the given Sylow subgroup. Every nonzero
proper subspace preserved by that full flag is one of its cuts, so the
partial flag can be rewritten in the same basis. Its index three forces
exactly one cut to be omitted. Both the prescribed projective equivalence
and the actual Sylow marking are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.959 (PDF p.976), using the intrinsic recognition
calculation also needed in 15.3.49(l). The index is a premise of this
geometric helper and is derived for the source group in LocalAlgebra.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Chapter1

private theorem flag_cut_coordinates {X : Type*} [Group X] {K : Subgroup X}
    {m : ℕ} (e : K ≃* PSL (m + 1)) (F : Flag (m + 1)) (b : Basis m)
    (h : cutStabilizer b Set.univ ≤ (flagStabilizer e F).map (linearModel e).toMonoidHom) :
    ∃ cuts : Set (Fin m),
      (flagStabilizer e F).map (linearModel e).toMonoidHom = cutStabilizer b cuts := by
  let cuts : Set (Fin m) := {i | cutSpace b i ∈ F.spaces}
  have hcut (W : Space (m + 1)) (hW : W ∈ F.spaces) :
      ∃ i : Fin m, W = cutSpace b i := by
    apply BinaryLinear.InvariantNodeActions.fullFlag_invariant_subspace b W
      (F.proper W hW).1 (F.proper W hW).2
    intro g hg
    obtain ⟨x, hx, rfl⟩ := h hg
    exact (mem_flagStabilizer e F x).mp hx W hW
  refine ⟨cuts, ?_⟩
  ext g
  obtain ⟨x, rfl⟩ := (linearModel e).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_flagStabilizer, mem_cutStabilizer]
  constructor
  · intro hx i hi
    exact hx (cutSpace b i) hi
  · intro hx W hW
    obtain ⟨i, rfl⟩ := hcut W hW
    exact hx i hW

/-- Retain the actual Sylow's complete basis flag as well as the deleted node. -/
theorem exists_deleted_basis_flag {X : Type*} [Group X] [Finite X]
    (K S P : Subgroup X) {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (e : K ≃* PSL (m + 1)) (hs : IsSylowIn 2 S K)
    (hSP : S ≤ P) (hPK : P ≤ K) (hi : S.relIndex P = 3) :
    ∃ (b : Basis m) (i : Fin m),
      P = ambientFlagStabilizer e (deletedFlag hm₀ b i) ∧
      (S.subgroupOf K).map (linearModel e).toMonoidHom = cutStabilizer b Set.univ := by
  obtain ⟨pos, hmodel⟩ := Linear.exists_position K S P (m + 1) (by omega) (by omega)
    e hs hSP hPK hi
  have hpos : P = ambientFlagStabilizer e pos.flag := by
    simpa only [hmodel] using pos.parabolic_eq
  obtain ⟨Q, hQ, hQP, hindex⟩ := model_inputs K S P (linearModel e) hs hSP hPK hi
  obtain ⟨b, hb⟩ := BinaryLinear.InvariantNodeActions.sylow_eq_cutStabilizer Q
  change (Q : Subgroup _) = cutStabilizer b Set.univ at hb
  have hmap : (P.subgroupOf K).map (linearModel e).toMonoidHom =
      (flagStabilizer e pos.flag).map (linearModel e).toMonoidHom := by
    simp only [hpos, ambientFlagStabilizer, subgroupOf,
      comap_map_eq_self_of_injective K.subtype_injective]
  have hfull : cutStabilizer b Set.univ ≤
      (flagStabilizer e pos.flag).map (linearModel e).toMonoidHom := by
    rw [← hmap]
    exact hb ▸ hQP
  obtain ⟨cuts, hc⟩ := flag_cut_coordinates e pos.flag b hfull
  have hPc : (P.subgroupOf K).map (linearModel e).toMonoidHom = cutStabilizer b cuts :=
    hmap.trans hc
  have hidx : (cutStabilizer b Set.univ).relIndex (cutStabilizer b cuts) = 3 := by
    simpa only [hb, hPc] using hindex
  obtain ⟨i, rfl⟩ := cuts_eq_compl_singleton_of_index_three b cuts hidx
  refine ⟨b, i, ?_, hQ.symm.trans hb⟩
  apply ambient_eq_of_linear_image e hPK
  rw [deletedFlag_stabilizer, map_comap_eq_self_of_surjective (linearModel e).surjective]
  exact hPc
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
