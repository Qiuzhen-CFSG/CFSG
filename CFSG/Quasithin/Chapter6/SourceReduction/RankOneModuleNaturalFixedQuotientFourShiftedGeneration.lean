module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourShiftedCenter
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter

/-!
# Generation using the Thompson center of a normal Sylow intersection

The original group supplies its actual E-generation witness. Its maximum
Thompson subgroup lies in a normal subgroup N, so the maximum elementary
families of P and P∩N agree. For each original minimal escaping E-member,
the original odd or component centralizer dichotomy applies. The shifted
center calculation and the literal conjugate-centralizer cover then control
its residual by centralizers of small-index subgroups of Ω₁Z(J_j(P∩N)).
This proves a containment criterion without asserting E-generation of N.

Source application: Aschbacher--Smith 6.1.4, printed p.665, and E.5.1--2.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
open ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem shifted_residual_le_of_core_center
    (P N A K M : Subgroup G) [N.Normal] (j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) 0) (hj : j < twoRank (P ⊓ N))
    (hK : IsEMemberAt j P A K)
    (hD : higherThompsonCenter (P ⊓ N) j ≤
      omegaOneCenterAmbient (higherThompsonCore (P ⊓ N) K j))
    (hc : ∀ D₁ : Subgroup G, D₁ ≤ higherThompsonCenter (P ⊓ N) j →
      Nat.log 2 (D₁.relIndex (higherThompsonCenter (P ⊓ N) j)) ≤ j →
      centralizer (D₁ : Set G) ≤ M) :
    (pResidual 2 K).map K.subtype ≤ M := by
  let S := P ⊓ N
  let D := higherThompsonCenter S j
  let W := higherThompsonCore S K j
  let E := omegaOneCenterAmbient W
  let B := A ⊓ (pCore 2 K).map K.subtype
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian W
  have hEW : E ≤ W := fun x hx => ((mem_omegaOneCenterAmbient_iff W x).mp hx).1
  have hES : E ≤ S := hEW.trans
    ((higherThompsonCore_le_thompsonJ S K j).trans (thompsonJ_le S j))
  have hWE : W ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mp
    exact fun x hx => mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff W x).mp hx).2.2
  have hBW : B ≤ W := by
    simpa only [Nat.zero_add] using inf_core_le_higherThompsonCore S A K 0 j hA
      (by simpa only [Nat.zero_add] using hj) hK.core_rank_le
  have hKE : K ≤ normalizer (E : Set G) := by
    have hn : K ≤ normalizer (W : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (higherThompsonCore_le S K j)).mp
        (shifted_higherThompsonCore_normal P N A K hK)
    intro k hk
    have hkW := hn hk
    rw [mem_normalizer_iff_map_conj_eq] at hkW ⊢
    change W.map (MulAut.conj k).toMonoidHom = W at hkW
    change (omegaOneCenterAmbient W).map (MulAut.conj k).toMonoidHom = _
    rw [← omegaOneCenterAmbient_map_injective (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective,hkW]
  have hindex : Nat.log 2 ((E ⊓ B).relIndex E) ≤ j := by
    simpa only [Nat.zero_add] using elementary_relativeIndex_le_of_thompsonFamily S A B E
      hA inf_le_left hK.core_rank_le hES (hBW.trans hWE)
  have hAE : A ≤ centralizer (E ⊓ B : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative A)).trans
      (centralizer_le (inf_le_right.trans inf_le_left))
  apply hK.1.residual_le_of_conjugates_le
  intro k hk
  obtain ⟨D₁,hD₁,hi,ha⟩ := conjugate_centralizer_cover D E (E ⊓ B) A K hD hKE hAE k hk
  exact ha.trans (hc D₁ hD₁ ((Nat.log_mono_right hi).trans hindex))

private theorem shifted_residual_le_of_centralizes_core
    (P N A K M : Subgroup G) (j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) 0) (hj : j < twoRank (P ⊓ N))
    (hK : IsEMemberAt j P A K)
    (hres : pResidual 2 K ≤ centralizer (pCore 2 K : Set K))
    (hc : ∀ D₁ : Subgroup G, D₁ ≤ higherThompsonCenter (P ⊓ N) j →
      Nat.log 2 (D₁.relIndex (higherThompsonCenter (P ⊓ N) j)) ≤ j →
      centralizer (D₁ : Set G) ≤ M) :
    (pResidual 2 K).map K.subtype ≤ M := by
  let S := P ⊓ N
  let D := higherThompsonCenter S j
  let B := A ⊓ (pCore 2 K).map K.subtype
  let _ : IsElementaryAbelian 2 D := omegaOneCenterAmbient_elementaryAbelian _
  have hAD : A ≤ centralizer (D : Set G) := by
    apply le_centralizer_iff.mp
    simpa only [Nat.zero_add] using higherThompsonCenter_le_centralizer S A 0 j hA
      (by simpa only [Nat.zero_add] using hj)
  have hr : Nat.log 2 ((D ⊓ B).relIndex D) ≤ j := by
    simpa only [Nat.zero_add] using elementary_relativeIndex_le_of_thompsonFamily S A B D
      hA inf_le_left hK.core_rank_le (higherThompsonCenter_le S j) (inf_le_left.trans hAD)
  have hh : (pResidual 2 K).map K.subtype ≤ centralizer
      ((pCore 2 K).map K.subtype : Set G) :=
    (map_mono hres).trans (map_centralizer_le_centralizer_image _ _)
  exact (hh.trans (centralizer_le
    (show D ⊓ B ≤ (pCore 2 K).map K.subtype from inf_le_right.trans inf_le_right))).trans
      (hc (D ⊓ B) inf_le_left hr)

/-- An original component E-member is controlled by the smaller Thompson
center, retaining its original quotient actor and its original component orbit. -/
theorem shifted_component_residual_le
    (P N A K M : Subgroup G) [N.Normal] (j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) 0) (hj : j < twoRank (P ⊓ N))
    (hK : IsEMemberAt j P A K) (he : ECaseComponent P A K)
    (hc : ∀ D₁ : Subgroup G, D₁ ≤ higherThompsonCenter (P ⊓ N) j →
      Nat.log 2 (D₁.relIndex (higherThompsonCenter (P ⊓ N) j)) ≤ j →
      centralizer (D₁ : Set G) ≤ M) :
    (pResidual 2 K).map K.subtype ≤ M := by
  rcases he.residual_centralizer_dichotomy with hz | hb
  · exact shifted_residual_le_of_centralizes_core P N A K M j hA hj hK hz hc
  · apply shifted_residual_le_of_core_center P N A K M j hA hj hK _ hc
    simpa only [Nat.zero_add] using shifted_higherThompsonCenter_le_omegaCenter
      P N A K 0 j hA hK (Or.inr ⟨he,hb⟩)

/-- The global maximum elementary family is unchanged on an intermediate
normal intersection containing the original maximum Thompson subgroup. -/
theorem maximal_thompsonFamily_inf_eq (P N : Subgroup G)
    (hJ : thompsonJ P 0 ≤ N) :
    thompsonFamily P 0 = thompsonFamily (P ⊓ N) 0 := by
  have hJS : elementaryAbelianMaxJ P ≤ P ⊓ N := by
    rw [← thompsonJ_zero]
    exact le_inf (thompsonJ_le P 0) hJ
  have hr := twoRank_eq_of_intermediate P (P ⊓ N) hJS inf_le_left
  ext A
  constructor
  · intro hA
    exact ⟨le_inf hA.1 ((show A ≤ thompsonJ P 0 from le_sSup hA).trans hJ),
      hA.2.1,hr ▸ hA.2.2⟩
  · intro hA
    exact ⟨hA.1.trans inf_le_left,hA.2.1,hr ▸ hA.2.2⟩

/-- Actual E-generation of the original group and centralizer control for
P∩N force containment. This does not assert any numerical parameter bound on N. -/
theorem eq_top_of_shifted_thompson_centralizers
    (P : Sylow 2 G) (N M : Subgroup G) [N.Normal] {j : ℕ}
    (hjpos : 0 < j) (hgen : IsEGenerated j G)
    (hJ : thompsonJ (P : Subgroup G) 0 ≤ N)
    (hj : j < twoRank ((P : Subgroup G) ⊓ N))
    (hNM : normalizer (thompsonJ (P : Subgroup G) 0 : Set G) ≤ M)
    (hc : ∀ D₁ : Subgroup G, D₁ ≤ higherThompsonCenter ((P : Subgroup G) ⊓ N) j →
      Nat.log 2 (D₁.relIndex (higherThompsonCenter ((P : Subgroup G) ⊓ N) j)) ≤ j →
      centralizer (D₁ : Set G) ≤ M) : M = ⊤ := by
  have hPM : (P : Subgroup G) ≤ M :=
    (P : Subgroup G).le_normalizer.trans
      ((normalizer_le_normalizer_thompsonJ _ 0).trans hNM)
  apply eq_top_of_minimal_thompson_residuals P 0 j hgen M hNM
  intro A K hA hmin
  have hAS : A ∈ thompsonFamily ((P : Subgroup G) ⊓ N) 0 :=
    maximal_thompsonFamily_inf_eq (P : Subgroup G) N hJ ▸ hA
  have hK := hmin.1.1
  rcases hK.1.2.2.2.2.2 with ho | he
  · rcases hmin.odd_centralizer_dichotomy hjpos hPM ho with hz | hb
    · exact shifted_residual_le_of_centralizes_core _ N A K M j hAS hj hK hz hc
    · apply shifted_residual_le_of_core_center _ N A K M j hAS hj hK _ hc
      simpa only [Nat.zero_add] using shifted_higherThompsonCenter_le_omegaCenter
        (P : Subgroup G) N A K 0 j hAS hK (Or.inl ⟨ho,hb⟩)
  · exact shifted_component_residual_le _ N A K M j hAS hj hK he hc

end CFSG.Quasithin.ChapterE
