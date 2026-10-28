module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.CubicFixedPoints
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-! A nontrivial normal subgroup of a Sylow two-group in the full orthogonal
four-dimensional action generates the full nine-group residual. We transport
the exact finite wreath theorem through the supplied faithful realization.
Source: the normal-closure step used in14.3.18(5). -/

public section
open Subgroup Theory.GroupTheory Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
theorem full_orthogonal_group_equiv
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : CFSG.Quasithin.ChapterG.Section09.FittingRecognition.OrthogonalRealization ρ ⊤) :
    Nonempty (D ≃* WreathTwoResidual.Actor) := by
  obtain ⟨e,_,_⟩ := hr
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨e.trans (topEquiv.trans
    ((CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
      BinaryFourPlus.isometryEquivWreath).trans
      (RegularWreathProduct.congr eSL.symm (MulEquiv.refl _))))⟩

theorem full_orthogonal_normal_sylow_residual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : CFSG.Quasithin.ChapterG.Section09.FittingRecognition.OrthogonalRealization ρ ⊤)
    (P : Sylow 2 D) (R : Subgroup D) (hle : R ≤ (P : Subgroup D))
    (hn : (P : Subgroup D) ≤ normalizer (R : Set D)) (hne : R ≠ ⊥) :
    (pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype = pResidual 2 D ∧
    Nat.card (pResidual 2 D) = 9 ∧
    ∃ r : D, r ∈ R ∧ orderOf r = 2 ∧
      ∀ x : D, x ∈ pResidual 2 D → r*x*r⁻¹=x⁻¹ := by
  obtain ⟨e⟩ := full_orthogonal_group_equiv ρ hr
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let R' := R.map e.toMonoidHom
  have hle' : R' ≤ (P' : Subgroup WreathTwoResidual.Actor) := map_mono hle
  have hn' : (P' : Subgroup WreathTwoResidual.Actor) ≤ normalizer (R' : Set _) :=
    (map_mono hn).trans (le_normalizer_map _)
  have hne' : R' ≠ ⊥ := by
    intro hb
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_bot]
    exact hb
  have heR : (normalClosure (R : Set D)).map e.toMonoidHom =
      normalClosure (R' : Set _) := map_normalClosure _ _ e.surjective
  have hr' := WreathTwoResidual.normalClosure_residual_eq P' R' hle' hn' hne'
  refine ⟨?_,?_,?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_embedded_pResidual,heR,map_pResidual]
    exact hr'
  · obtain ⟨ee⟩ := WreathTwoResidual.residual_equiv_elementaryNine
    rw [Nat.card_congr (e.subgroupMap (pResidual 2 D)).toEquiv]
    change Nat.card ((pResidual 2 D).map e.toMonoidHom) = 9
    rw [map_pResidual 2 e,Nat.card_congr ee.toEquiv]
    norm_num [Nat.card_fun,Nat.card_zmod]
  · obtain ⟨r,hr,hord,hinv⟩ :=
      WreathTwoResidual.exists_normal_sylow_inverter P' R' hle' hn' hne'
    obtain ⟨a,ha,hea⟩ := hr
    change e a = r at hea
    refine ⟨a,ha,?_,?_⟩
    · rw [← e.orderOf_eq a,hea]
      exact hord
    · intro x hx
      apply e.injective
      simp only [map_mul,map_inv,hea]
      exact hinv (e x) ((map_pResidual 2 e) ▸ (mem_map_of_mem e.toMonoidHom hx))

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
