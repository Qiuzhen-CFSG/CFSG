module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Assembly

/-!
# Consuming one actual embedding conclusion

The original embedding branches and residual proof use only the conclusion
on the given contrary overgroup. Exposing that exact local consumption lets
the adequate intrinsic theorem retain and separately exclude Held, without
assuming its old stronger universal companion. All model exclusions, outer
actions and literal residual maps are the existing source arguments.
Source: Aschbacher--Smith, 15.4.20, pp.1163--1164.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}
open Chapter1

/-- The ordinary alternatives need only this actual embedding conclusion. -/
theorem PlacedX.two_branches_of_conclusion (hG : IsSimpleQTKE κ G)
    (orbits : ComponentOrbitTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX)
    (conclusion : Chapter1.XiEmbedding.Conclusion 3 U d.wholeX
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) H) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn H ∧
      IsQuasisimple (Chapter1.XiQuotient L) ∧
      IsSimpleGroup (Chapter1.XiQuotient L) ∧ d.wholeX ≤ componentOrbit L U ∧
      Nonempty (P₀ ≃* Chapter1.XiEmbedding.Plane 3) ∧
      Nonempty (Chapter1.XiEmbedding.automizer U P₀ ≃* DihedralGroup 4) ∧
      ((Chapter1.XiEmbedding.SwappedFactors U P₀ L ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient L) ∧
          (normalizer (L.subgroupOf H : Set H)).index = 2) ∨
        ((L.subgroupOf H).Normal ∧ d.wholeX ≤ L ∧
          (ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 4 2 ∨
            ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 5 2) ∧
          Nonempty (Chapter1.XiQuotient (L ⊔ U) ≃*
            MulAut (Chapter1.XiQuotient L)))) := by
  obtain ⟨hsq, hlocal, hSylow, hD⟩ := h.embedding_input hG P
  rcases conclusion with hn | ⟨L, hL, hq, hX, ha⟩
  · exact (h.not_normal hn).elim
  obtain ⟨he, ha⟩ := alternatives_of_dihedral ha hD
  have ho := orbits G hG H h.overgroup.1 L hL
  rw [ncard_conjugates_eq_index_normalizer] at ho
  have hUH : U ≤ H := le_sup_right.trans hlocal.overgroup
  rcases ha with ⟨hs, hm⟩ | ⟨hn, hm⟩
  · have hi : (normalizer (L.subgroupOf H : Set H)).index = 2 := by
      rcases ho with hn | ⟨hi, _⟩
      · exact (hs.1 (hUH.trans ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn))).elim
      · exact hi
    exact ⟨L, hL, hq, swapped_model_simple hq hm, hX, he, hD, Or.inl ⟨hs, hm, hi⟩⟩
  · have hLn := normal_of_sylow_normalizes hL.1 hSylow hn (ho.imp_right And.left)
    have hXL : d.wholeX ≤ L := (componentOrbit_eq_of_normalizes hn) ▸ hX
    have hmodel : ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 4 2 ∨
        ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 5 2 := by
      rcases hm with hthree | heleven | hfour | hfive
      · exact (SmallModels.not_linearThreeModel hlocal hSylow hL.1 hLn hXL hD hthree).elim
      · exact (SmallModels.not_mathieuEleven hlocal hSylow hL.1 hLn hXL hD heleven).elim
      · exact Or.inl hfour
      · exact Or.inr hfive
    have hz : center (Chapter1.XiQuotient L) = ⊥ := by
      rcases hmodel with hm | hm
      · exact binary_linear_center_eq_bot (by decide : 0 < 4) hm
      · exact binary_linear_center_eq_bot (by decide : 0 < 5) hm
    exact ⟨L, hL, hq, simple_of_quasisimple_center_bot hq hz, hX, he, hD,
      Or.inr ⟨hLn, hXL, hmodel,
        BinaryAction.binary_quotient_aut hsq hlocal hSylow hL hLn hXL hq hD hmodel⟩⟩


/-- The literal residual follows from the same local conclusion. -/
theorem PlacedX.normalClosure_branches_of_conclusion (hG : IsSimpleQTKE κ G)
    (orbits : ComponentOrbitTheorem κ)
    (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX)
    (conclusion : Chapter1.XiEmbedding.Conclusion 3 U d.wholeX
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) H) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K) := by
  obtain ⟨hsq, hlocal, _, _⟩ := h.embedding_input hG P
  obtain ⟨L, hL, hq, hs, hX, _, _, hb⟩ := h.two_branches_of_conclusion hG orbits P conclusion
  rcases hb with ⟨hswap, hm, hi⟩ | ⟨hn, hXL, hm, haut⟩
  · have hr := swapped_normalClosure_eq_residual hG residual h.overgroup.1
      hlocal hL hs hX hswap hi
    have he := swapped_normalClosure_eq_orbit hlocal hL hs hX hswap hi
    obtain ⟨t, ht, hmove, hP, hdisj, hcomm⟩ := hswap.2
    have hpair : normalClosureIn d.wholeX H = L ⊔ L.conjBy t :=
      he.1.trans (componentOrbit_eq_pair_of_index_two le_rfl hL.1 hi
        ((le_sup_right.trans hlocal.overgroup) ht.1) hmove)
    have hKN : normalClosureIn d.wholeX H ≤ normalizer L :=
      he.1.le.trans (componentOrbit_le_normalizer hL)
    have hLK : L ≤ normalClosureIn d.wholeX H := le_sup_left.trans hpair.ge
    have hproduct : (normalClosureIn d.wholeX H : Set G) =
        (L : Set G) * (L.conjBy t : Set G) := by
      exact (congrArg (fun A : Subgroup G => (A : Set G)) hpair).trans
        (coe_mul_of_right_le_normalizer_left _ _ ((le_sup_right.trans hpair.ge).trans hKN))
    exact ⟨hr, Or.inr ⟨L, t, hL, hq, hs, hm, ht, hmove, hi, hpair, hproduct,
      (normal_subgroupOf_iff_le_normalizer hLK).mpr hKN, hP, hdisj, hcomm⟩⟩
  · have hk := h.normalClosure_eq_component hXL hL.1 hn (cComponent_twoPerfect hL) hs
    have hr : normalClosureIn d.wholeX H = (primeToResidual 3 H).map H.subtype :=
      le_antisymm h.normalClosure_le_residual
        ((binary_residual_le hsq hlocal hL hn hXL hm).trans hk.ge)
    refine ⟨hr, Or.inl ?_⟩
    rw [hk]
    exact ⟨hL, hn, hq, hs, hm, haut⟩


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
