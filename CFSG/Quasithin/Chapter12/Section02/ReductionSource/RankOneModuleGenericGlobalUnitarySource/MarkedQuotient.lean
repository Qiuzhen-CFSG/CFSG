module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen module's simultaneous short-root quotient marking

The whole-reduced-module input applies the prepared theorem to the same
short root, long root and full line. The long root belongs to the original
right-residual center and has the ambient common-centralizer bound;
it survives the exact line quotient and represents every nonzero vector.
The original hypotheses, q=4, degree-two rows and both orientations remain.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295–296,659,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The same original short and long roots supply common-centralizer control,
the exact short-line quotient, and simultaneous quotient fusion. -/
theorem rankOne_unitary_marked_short_quotient
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ (∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v) ∧
      ∀ (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)),
        s ⊆ V.map f →
        ∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
          (∀ x ∈ s, g*x*g⁻¹ ∈ V.map f) →
          ∃ a : UnitarySource.shortLineNormalizer L t U,
            a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
              QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
                (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_marked_short_quotient hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
