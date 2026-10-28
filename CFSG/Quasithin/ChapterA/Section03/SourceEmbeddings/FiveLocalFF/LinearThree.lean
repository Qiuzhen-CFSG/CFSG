module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.RankOneCovers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Actual local A₅ sections in the projective three-space

Conjugate the full Sylow to the standard unipotent subgroup. Its proper
join with the local C-component lies in a point or line parabolic.
Perfectness puts the component in that parabolic's affine residual, which
already contains the standard Sylow. Rank-one core-cover rigidity then
identifies the original component with the literal residual. Its A₅
core quotient forces the field to have four elements.

The image theorem keeps the original map and its restricted two-kernel.
Source: Aschbacher–Smith A.3.12 and 10.2.9, pp.47–48 and 751–752.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_perfect {G : Type*} [Group G] (S : Subgroup G)
    {B : Subgroup G} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

theorem linear_three_local_placement {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ g : PSL(3,F), B.map (MulAut.conj g).toMonoidHom = pointLocal F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocal F := by
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  have hjoin : B ⊔ (S : Subgroup PSL(3,F)) ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      have hm := hB
      change (B.subgroupOf (B ⊔ (S : Subgroup PSL(3,F)))).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) S (unipotentSylow F (by omega) hF)
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hS : (S' : Subgroup PSL(3,F)) = unipotent F := congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl : B.map a.toMonoidHom ∈ localCComponents (S' : Subgroup PSL(3,F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := local_perfect (S' : Subgroup PSL(3,F)) hl
  have hproper' : (B ⊔ (S : Subgroup PSL(3,F))).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hjoin
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [ht, map_top_of_surjective _ a.surjective]
  have hU : unipotent F ≤ (B ⊔ (S : Subgroup PSL(3,F))).map a.toMonoidHom :=
    hS ▸ map_mono (show (S : Subgroup PSL(3,F)) ≤ B ⊔ (S : Subgroup PSL(3,F)) from le_sup_right)
  obtain hp | hp := UnipotentOvergroups.overgroup_unipotent F _ hU hproper'
  · refine ⟨g,Or.inl ?_⟩
    let := pointLocal_isPerfect F hlarge
    apply local_eq_of_sl2_core_quotient (pointLocal F) (by omega)
      (pointLocalCoreQuotientEquiv F) S' (B.map a.toMonoidHom) hl
    · rw [← ParabolicResiduals.pointParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono le_sup_left).trans hp)
    · rw [hS]
      exact unipotent_le_pointLocal F
  · refine ⟨g,Or.inr ?_⟩
    let := lineLocal_isPerfect F hlarge
    apply local_eq_of_sl2_core_quotient (lineLocal F) (by omega)
      (lineLocalCoreQuotientEquiv F) S' (B.map a.toMonoidHom) hl
    · rw [← ParabolicResiduals.lineParabolic_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono le_sup_left).trans hp)
    · rw [hS]
      exact unipotent_le_lineLocal F

theorem linear_three_five_section_placement {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : PSL(3,F),
      B.map (MulAut.conj g).toMonoidHom = pointLocal F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocal F := by
  obtain ⟨g,hg⟩ := linear_three_local_placement hF hn S B hB hproper
  refine ⟨?_,g,hg⟩
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F := by
      rw [hp]
      exact pointLocalCoreQuotientEquiv F
    exact field_four_of_sl2_five_section e (aq.trans ep)
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F := by
      rw [hp]
      exact lineLocalCoreQuotientEquiv F
    exact field_four_of_sl2_five_section e (aq.trans ep)

theorem linear_three_five_section_image {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : G →* PSL(3,F)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (hproper : L.map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : PSL(3,F),
      (L.map f).map (MulAut.conj g).toMonoidHom = pointLocal F ∨
      (L.map f).map (MulAut.conj g).toMonoidHom = lineLocal F := by
  let := hks
  exact linear_three_five_section_placement hF hn
    (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f) hproper
    (((f.subgroupMap L).quotientPCoreEquivOfSurjective
      (f.subgroupMap_surjective L) hk).symm.trans e)
end
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
