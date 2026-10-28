module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityThree

/-!
# Parity from the remaining normalizer geometry

The original Hypothesis1223 and ChosenModule hypotheses supply the natural
marking and residual maximality/nonfaithfulness. Point TI inside the literal
residual normalizer consequently globalizes. The abelian full point-normalizer
span gives intersecting-conjugate commutation, and the FSU supplies the other
module and generated-core requirements of F.8.1.

The final parity adapter consumes the completed displacement and both terminal
critical-pair branches. It still requires the original G.2 geometry, abelian
normalizer span, quotient-action kernel bound and residual-normalizer TI.
Discharging these inputs, including the earlier source 5.1.16(2), remains with
qt-d-1222-linear-field-parity. This is a conditional assembly, not the source
5.1.17 theorem.

Source: Aschbacher–Smith 5.1.17, pp.640–642, applied in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The chosen point is globally TI once TI in the residual normalizer is established. -/
theorem rankOne_point_global_ti_of_residual_ti
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A : Subgroup G} (hodd : Odd n)
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    ChapterI.Section06To08.IsTISubgroup (setup T L V H A).V₁ := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hf := fundamental_point_global_ti_of_residual_ti F D.sylow_normalizes_component
    hpsl hodd hnat hH.1.1 hm hnf (he.symm ▸ hti)
  simpa only [he] using hf

/-- The literal chosen-module F.8 setup, deriving its commutation and FSU clauses. -/
theorem rankOne_f8_of_normalizer_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A : Subgroup G} (hodd : Odd n)
    (hti : ∀ g ∈ normalizer (residual H : Set G),
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    (hg2 : ChapterG.Section02.Setup.Hypothesis (setup T L V H A))
    (hab : IsMulCommutative (conjugateSpanBy V (setup T L V H A).G₁))
    (hker : ((setup T L V H A).quotientCentralizer hg2.H_le V).normalCore ≤
      pCore 2 (H ⊔ A : Subgroup G)) :
    (setup T L V H A).Hypothesis := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  subst V
  exact fundamental_f8_of_normalizer_span F D.sylow_normalizes_component hpsl hodd hnat
    hH hm hnf hti hg2 hab hker

/-- Both terminal parity branches now consume the remaining normalizer geometry. -/
theorem rankOne_even_exponent_of_normalizer_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      ∃ hg2 : ChapterG.Section02.Setup.Hypothesis (setup T L V H A),
        IsMulCommutative (conjugateSpanBy V (setup T L V H A).G₁) ∧
        ((setup T L V H A).quotientCentralizer hg2.H_le V).normalCore ≤
          pCore 2 (H ⊔ A : Subgroup G) ∧
        ∀ g ∈ normalizer (residual H : Set G),
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    Even n := by
  apply D.rankOne_even_exponent_of_chosen_geometry h hmany hn hpsl hH hgen hlinear
  intro A B c ho
  obtain ⟨hg2,hab,hker,hti⟩ := hgeometry A B c ho
  refine ⟨D.rankOne_f8_of_normalizer_span h hmany hn hpsl hH hlinear ho hti hg2 hab hker,?_⟩
  have ht := D.rankOne_point_global_ti_of_residual_ti h hmany hn hpsl hH hlinear ho hti
  intro g
  by_cases hg : g ∈ normalizer ((setup T L V H A).V₁ : Set G)
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · left
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.2
    have hy1 := (ChapterI.Section06To08.isTISubgroup_iff _).mp ht g hg y hy (by
      change (MulAut.conj g).toMonoidHom y ∈ (setup T L V H A).V₁
      rw [he]
      exact hx.1)
    simpa only [hy1,map_one,mem_bot] using he.symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
