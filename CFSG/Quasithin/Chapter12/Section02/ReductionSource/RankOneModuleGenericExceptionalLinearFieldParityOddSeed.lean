module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSeed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearField

/-!
# Irreducibility of the selected FSU module in the parity argument

The original chosen-module setup and the completed exceptional-residual
analysis give C_{Ω₁(Z(T))}(L)=1. In odd degree the FSU module equals its
original seed, has no fixed vectors and is irreducible. In particular its
TI property under N_G(L) no longer requires a natural marking.

A natural marking of the seed's fixed quotient lifts to the entire FSU
module. The final parity application uses this lift, retaining the
classification, global point TI, F.8 and displacement obligations with
qt-d-1222-linear-field-parity. These are explicit remaining inputs, not
source theorems asserted by this module.

Source: Aschbacher–Smith, 5.1.17, printed p.640, applied in 12.2.2,
printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The original hypotheses remove the fixed kernel of every selected FSU module. -/
theorem rankOne_fundamental_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) :
    F.moduleSubgroup ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact fundamental_fixed_eq_bot F D.sylow_normalizes_component
    (D.linear_field_source_geometry h.toHypothesis1221 hH hm hf).2.1

/-- The actual FSU seed is the whole irreducible module, and its normalizer
conjugates satisfy TI, without assuming the natural-module conclusion. -/
theorem rankOne_odd_fundamental_seed_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) :
    F.moduleSubgroup = F.seed ∧
      (∀ E : Subgroup G, E ≤ F.moduleSubgroup → L ≤ normalizer (E : Set G) →
        E = ⊥ ∨ E = F.moduleSubgroup) ∧
      ∀ g ∈ normalizer (L : Set G),
        F.moduleSubgroup ⊓ F.moduleSubgroup.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          F.moduleSubgroup.map (MulAut.conj g).toMonoidHom = F.moduleSubgroup := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hZ := (D.linear_field_source_geometry h.toHypothesis1221 hH hm hf).2.1
  exact ⟨fundamental_module_eq_seed_of_odd F D.sylow_normalizes_component hpsl hodd,
    fundamental_invariant_subgroup_of_odd F D.sylow_normalizes_component hpsl hodd hZ,
    fun _ hg => fundamental_module_ti_of_odd F D.sylow_normalizes_component hpsl hodd hZ hg⟩

/-- Only the natural fixed-quotient classification remains in the marking step. -/
theorem rankOne_odd_fundamental_natural_of_seed_fixed_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hq : Chapter6.Source.IsNaturalFixedQuotient L F.seed n) :
    Chapter6.Source.IsNaturalModule L F.moduleSubgroup n := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact fundamental_natural_of_seed_fixed_quotient F D.sylow_normalizes_component hpsl hodd
    (D.linear_field_source_geometry h.toHypothesis1221 hH hm hf).2.1 hq

/-- Literal parity assembly after the seed and fixed-kernel reductions. -/
theorem rankOne_even_exponent_of_seed_quotient_geometry_and_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      ∃ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L,
        Chapter6.Source.IsNaturalFixedQuotient L F.seed n ∧
        (setup T L F.moduleSubgroup H A).Hypothesis ∧
        ∀ g : G,
          (setup T L F.moduleSubgroup H A).V₁ ⊓
              (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L F.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
              (setup T L F.moduleSubgroup H A).V₁)
    (hlower : DisplacementSource T L H n) : Even n := by
  apply D.rankOne_even_exponent_of_fundamental_geometry_and_displacement
    h hmany hn hpsl hH hgen hlinear ?_ hlower
  intro A B c hodd
  obtain ⟨F,hq,hf,hti⟩ := hgeometry A B c hodd
  exact ⟨F,D.rankOne_odd_fundamental_natural_of_seed_fixed_quotient h hmany hpsl hH
    hlinear hodd F hq,hf,hti⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
