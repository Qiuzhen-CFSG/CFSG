module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityGeometry

/-!
# Parity after constructing the quotient-action kernel bound

The chosen natural module and the actual product HD_L/O₂(HD_L) prove
F.8.1(c). A normal kernel containing the exceptional residual would
normalize V, contrary to maximal-local uniqueness. The remaining central
Cartan factor acts faithfully on V/Z₁ and has trivial intersection with
the kernel. This removes the quotient-kernel premise from the parity
consumer without assuming abelianness of the normalizer span.

The remaining source construction belongs to qt-d-1222-linear-field-parity:
5.1.16(2), TI inside the residual normalizer and the abelian normalizer span.
The theorem here is conditional on the latter two geometric statements;
it does not assert unconditional parity.

Source: Aschbacher–Smith 5.1.17, p.641, applied in 12.2.2, p.795
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

/-- F.8.1(c) on the literal HD_L and V/Z₁, from the standing hypotheses. -/
theorem rankOne_odd_quotient_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    ((setup T L V H A).quotientCentralizer
      (D.rankOne_odd_g2 h hmany hn hpsl hH hlinear c hodd).H_le V).normalCore ≤
        pCore 2 (H ⊔ A : Subgroup G) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_quotient_kernel hi hH c hodd hm hnf hlinear F hnat

/-- The parity assembly now retains only TI and abelianness of the normalizer span. -/
theorem rankOne_even_exponent_of_normalizer_ti_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ (A B : Subgroup G) (_c : CartanPair T L H A B) (_ho : Odd n),
      IsMulCommutative (conjugateSpanBy V (setup T L V H A).G₁) ∧
        ∀ g ∈ normalizer (residual H : Set G),
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    Even n := by
  apply D.rankOne_even_exponent_of_normalizer_ti_span_kernel h hmany hn hpsl hH hgen hlinear
  intro A B c ho
  exact ⟨(hgeometry A B c ho).1,
    D.rankOne_odd_quotient_kernel h hmany hn hpsl hH hlinear c ho,(hgeometry A B c ho).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
