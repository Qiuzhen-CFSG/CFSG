module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNonabelian
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityKernel

/-!
# The nonabelian normalizer-span branch of the parity argument

Under the original chosen-module hypotheses, odd field degree gives the natural
marking. If the full point-normalizer span is nonabelian, G.2.3 supplies its
actual two-conjugate generated group and core layers. If that generated core
lies in the point-normalizer core, its middle layer collapses: O₂(L) is
elementary abelian and [O₂(L),L] is the original chosen natural module.

These results construct the local branch used on printed pp.640–641. They do
not assert that the core containment holds, exclude the resulting block, or
construct global TI. Those source obligations, including 5.1.16(2), remain
with the final parity assembly qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.17, pp.640–641, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The literal nonabelian branch, with every natural marking premise discharged. -/
theorem rankOne_odd_nonabelian_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L V).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L V).G₁) :
    let E := normalizerSetup T L V
    E.I l = L ⊔ E.U ∧
      E.S l = E.W l ⊔ ChapterG.Section02.Setup.conjugate (E.W l) l ∧
      E.V ≤ E.S₂ l ∧ E.S₂ l ≤ E.S l ∧
      IsElementaryAbelian 2 (E.S₂ l) ∧ ⁅E.S₂ l,E.I l⁆ ≤ E.V ∧
      E.V ≤ centralizer (E.S l : Set G) ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (E.S l : Set G) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_nonabelian_geometry hi hH c hodd hm hnf F hnat hnon hl hlout

/-- The source block-layer equality follows from the remaining core containment;
no quotient recognition or constituent assumption is needed. -/
theorem rankOne_odd_nonabelian_core_collapse
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L V).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L V).G₁)
    (hcore : (normalizerSetup T L V).S l ≤ (normalizerSetup T L V).QH) :
    let E := normalizerSetup T L V
    E.S l = E.S₂ l ∧ IsElementaryAbelian 2 (L.pCoreIn 2) ∧ ⁅L.pCoreIn 2,L⁆ = V := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_nonabelian_core_collapse hi hH c hodd hm hnf F hnat hnon hl hlout hcore

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
