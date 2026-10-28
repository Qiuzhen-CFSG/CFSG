module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.Replacement
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
/- The source specialization is an internal continuation of Replacement;
   its residual-intermediate lemma stays private to that implementation. -/
import all CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.Replacement

/-!
# Actual component orbits in the 15.4 contrary configuration

The intrinsic embedding theorem and the SQTK normal-or-index-two theorem are
applied to the original quotient maps. This gives the binary, exchanged and
Held alternatives, and retains them upon replacing H by its residual times U.
Only the genuine two-orbit residual theorem remains an earlier source input.
Source: Aschbacher--Smith, 1.2.1--2, 1.3.4 and 15.4.19--20.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}
open Chapter1
theorem PlacedX.two_branches_of_conclusion_sourceOrbit (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  have ho := Section02.component_normal_or_index_two_source hsq hL.2
  have hUH : U ≤ H := le_sup_right.trans hlocal.overgroup
  rcases ha with ⟨hs, hm⟩ | ⟨hn, hm⟩
  · have hi : (normalizer (L.subgroupOf H : Set H)).index = 2 := by
      rcases ho with hn | hi
      · exact (hs.1 (hUH.trans ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn))).elim
      · exact hi
    exact ⟨L, hL, hq, swapped_model_simple hq hm, hX, he, hD, Or.inl ⟨hs, hm, hi⟩⟩
  · have hLn := normal_of_sylow_normalizes hL.1 hSylow hn ho
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


theorem PlacedX.normalClosure_branches_of_conclusion_sourceOrbit (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX)
    (conclusion : Chapter1.XiEmbedding.Conclusion 3 U d.wholeX
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) H) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K) := by
  obtain ⟨hsq, hlocal, _, _⟩ := h.embedding_input hG P
  obtain ⟨L, hL, hq, hs, hX, _, _, hb⟩ := h.two_branches_of_conclusion_sourceOrbit hG P conclusion
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


theorem PlacedX.normalClosure_adequate_sourceOrbit (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K ∨ HeldCase H K) := by
  obtain ⟨hsq, hlocal, hSylow, _⟩ := h.embedding_input hG P
  rcases XiEmbedding.adequateLocalEmbeddingTheorem_knownSimple G 3 U d.wholeX _ H hlocal hsq hSylow with hn | ⟨L,hL,hq,hX,ha⟩
  · exact (h.not_normal hn).elim
  rcases ha with ha | ⟨_, _, hn, ⟨e⟩⟩
  · have hc : XiEmbedding.Conclusion 3 U d.wholeX
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) H := Or.inr ⟨L,hL,hq,hX,ha⟩
    obtain ⟨hr, hb⟩ := h.normalClosure_branches_of_conclusion_sourceOrbit hG residual P hc
    exact ⟨hr, hb.elim Or.inl (Or.inr ∘ Or.inl)⟩
  · have ho := Section02.component_normal_or_index_two_source hsq hL.2
    have hLn := normal_of_sylow_normalizes hL.1 hSylow hn ho
    have hXL : d.wholeX ≤ L := (componentOrbit_eq_of_normalizes hn) ▸ hX
    have hs := simple_of_quasisimple_center_bot hq (held_model_center_bot e)
    have hk := h.normalClosure_eq_component hXL hL.1 hLn (cComponent_twoPerfect hL) hs
    have hr := le_antisymm h.normalClosure_le_residual
      ((held_residual_le hsq hlocal hL hLn hXL e).trans hk.ge)
    refine ⟨hr, Or.inr (Or.inr ?_)⟩
    rw [hk]
    exact ⟨hL, hLn, hq, ⟨e⟩⟩


theorem ExchangedCase.restrict_sourceOrbit (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {D P K : Subgroup G}
    (hc : ExchangedCase H U P K) (hKD : K ≤ D) (hUD : U ≤ D)
    (hDH : D ≤ H) (hD : D ∈ Chapter1.H G) : ExchangedCase D U P K := by
  obtain ⟨L, t, hL, hq, hs, hm, ht, hmove, _, hK, hprod, hn, hP, hd, hcomm⟩ := hc
  have hLD : L ≤ D := (le_sup_left.trans hK.ge).trans hKD
  have hL' : L ∈ cComponentsIn D := ⟨hLD, hL.2.subgroupOf_of_le hLD hDH⟩
  have hi : (normalizer (L.subgroupOf D : Set D)).index = 2 := by
    have ho := Section02.component_normal_or_index_two_source (RadicalExclusions.sqtk_of_mem_H hG hD) hL'.2
    rcases ho with hn | hi
    · exact (hmove (((normal_subgroupOf_iff_le_normalizer hLD).mp hn) (hUD ht.1))).elim
    · exact hi
  exact ⟨L, t, hL', hq, hs, hm, ht, hmove, hi, hK, hprod, hn, hP, hd, hcomm⟩


theorem PlacedX.adequate_replacement_sourceOrbit (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    let D := K ⊔ U
    ∃ _hD : PlacedX d i j D U,
      K = normalClosureIn d.wholeX D ∧ K = (primeToResidual 3 D).map D.subtype ∧
      (BinaryCase D U K ∨ ExchangedCase D U P₀ K ∨ HeldCase D K) := by
  obtain ⟨hK, hb⟩ := h.normalClosure_adequate_sourceOrbit hG residual P
  have hrepl := h.residual_replacement
  dsimp only at hrepl
  rw [← hK] at hrepl
  obtain ⟨hD, hU, _, hcore⟩ := hrepl
  obtain ⟨placed⟩ := h.replacement_configuration hD hU hcore
  have hUH : U ≤ H := h.sylow_image ▸ map_subtype_le (h.sylow : Subgroup H)
  have hDH : normalClosureIn d.wholeX H ⊔ U ≤ H :=
    sup_le (normalClosureIn_le_overgroup _ _) hUH
  have hres := embedded_residual_eq_of_intermediate 3 hK le_sup_left hDH
  refine ⟨placed, hres.trans
    (placed.normalClosure_adequate_sourceOrbit hG residual P).1.symm, hres, ?_⟩
  rcases hb with hb | he | hh
  · exact Or.inl (hb.restrict le_sup_left hDH)
  · exact Or.inr (Or.inl (he.restrict_sourceOrbit hG le_sup_left le_sup_right hDH hD.1))
  · exact Or.inr (Or.inr (hh.restrict le_sup_left hDH))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction

