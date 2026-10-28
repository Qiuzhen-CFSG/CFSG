module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFour
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# Small elementary actions of an exceptional local component

Every proper kernel of a local C-component is solvable. A nontrivial action
on a binary elementary group of order at most sixteen would thus retain the
original exceptional simple section inside GL₄(2), which the proved carrier
separation excludes. Consequently the literal conjugation action is trivial.

This supplies the small elementary subgroup branch of the J₄ exclusion in
Aschbacher–Smith A.3.12 and 5.1.12, printed pp.47–48 and635. No order-based
identification of PSL₃(4) with PSL₄(2) is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem exceptional_binary_four_hom_trivial
    {G : Type*} [Group G] [Finite G] {S B : Subgroup G}
    (hB : B ∈ localCComponents S)
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B))
    (f : B →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : f = 1 := by
  apply MonoidHom.ker_eq_top_iff.mp
  by_contra hker
  have ht : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le (le_refl B) le_sup_left
  have hk := kernel_le_solvableRadical_of_top_isCComponent ht f hker
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hk) (inclusion_injective hk)
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let := Exceptional.local_perfect hB
  let := hm.isSimple
  have hmod := hm.of_equiv (PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    f.rangeRestrict f.rangeRestrict_surjective).symm
  apply Exceptional.not_section_of_binaryFour f.range hmod
  let e := (BinaryLinear.OuterCyclic.matrixEquivLinear 4).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).symm
  exact ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨e⟩⟩

/-- An exceptional local component acts trivially on every normalized elementary
binary group of order at most sixteen. The action is actual conjugation. -/
theorem exceptional_centralizes_small_elementary
    {G : Type*} [Group G] [Finite G] {S B E : Subgroup G}
    (hB : B ∈ localCComponents S)
    (hm : Exceptional.IsModel (B ⧸ pCore 2 B))
    [IsElementaryAbelian 2 E] (hE : Nat.card E ≤ 16)
    (hn : B ≤ normalizer (E : Set G)) : B ≤ centralizer (E : Set G) := by
  obtain ⟨j,hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 4) E hE
  let a := E.normalizerMonoidHom.comp (inclusion hn)
  have ha := exceptional_binary_four_hom_trivial hB hm (j.comp a)
  intro b hb
  have he : a ⟨b,hb⟩ = 1 := hj (by
    have hh := DFunLike.congr_fun ha (⟨b,hb⟩ : B)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, map_one] using hh)
  have hk : inclusion hn (⟨b,hb⟩ : B) ∈ E.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
