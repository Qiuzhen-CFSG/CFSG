module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityFusion

/-!
# Parity with the G.2 setup constructed

The original Hypothesis1223 and ChosenModule provide the odd natural
marking and residual maximality/nonfaithfulness. The Borel calculation
therefore verifies G.2.1 on the literal HD_L and on the full point normalizer,
including irreducibility of V/Z₁. The latter lies in the original residual
normalizer, and its conjugate span has the G.2.2 core and Frattini bounds.

The parity consumer removes the former G.2 callback and retains exactly
residual-normalizer TI, abelianness of the full normalizer span and the
F.8 quotient-action kernel bound. Those source inputs, including 5.1.16(2),
remain with qt-d-1222-linear-field-parity; this is not unconditional parity.

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

/-- The literal chosen-module G.2.1 setup, under the original standing hypotheses. -/
theorem rankOne_odd_g2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    ChapterG.Section02.Setup.Hypothesis (setup T L V H A) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  simpa only [he] using fundamental_g2 hi hH c hodd hm hnf F hnat

/-- G.2.1 also holds at the full normalizer of the original chosen point. -/
theorem rankOne_odd_g2_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    (ChapterG.Section02.Setup.mk V (setup T L V H A).V₁ L T
      (setup T L V H A).G₁).Hypothesis := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  simpa only [he] using fundamental_g2_normalizer hi hH c hodd hm hnf F hnat

/-- The actual point normalizer is contained in the residual normalizer. -/
theorem rankOne_odd_point_normalizer_le_residual_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    (setup T L V H A).G₁ ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  simpa only [he] using fundamental_point_normalizer_le_residual_normalizer hi hH c hodd hm hnf F hnat

/-- Core, Frattini and commutator bounds on the original full normalizer span. -/
theorem rankOne_odd_normalizer_span_reductions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    let E := setup T L V H A
    let U := conjugateSpanBy V E.G₁
    U ≤ E.G₁.pCoreIn 2 ∧ U ≤ (T : Subgroup G) ∧
      (frattini U).map U.subtype ≤ E.V₁ ∧ ⁅U,E.G₁.pCoreIn 2⁆ ≤ E.V₁ := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_normalizer_span_reductions hi hH c hodd hm hnf F hnat

/-- G.2 is now constructed; only TI, the abelian span and the quotient kernel remain. -/
theorem rankOne_even_exponent_of_normalizer_ti_span_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ (A B : Subgroup G) (c : CartanPair T L H A B) (ho : Odd n),
      IsMulCommutative (conjugateSpanBy V (setup T L V H A).G₁) ∧
        ((setup T L V H A).quotientCentralizer
          (D.rankOne_odd_g2 h hmany hn hpsl hH hlinear c ho).H_le V).normalCore ≤
            pCore 2 (H ⊔ A : Subgroup G) ∧
        ∀ g ∈ normalizer (residual H : Set G),
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    Even n := by
  apply D.rankOne_even_exponent_of_normalizer_geometry h hmany hn hpsl hH hgen hlinear
  intro A B c ho
  exact ⟨D.rankOne_odd_g2 h hmany hn hpsl hH hlinear c ho,hgeometry A B c ho⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
