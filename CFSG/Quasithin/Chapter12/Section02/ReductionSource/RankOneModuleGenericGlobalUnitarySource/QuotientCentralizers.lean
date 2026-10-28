module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.QuotientCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen module's ambient short-quotient centralizers

The whole-reduced-module input supplies the prepared row. Its original
marked roots and complete short line give centralizer and transporter
bounds in N_{C_G(t)}(U)/U, with every nontrivial quotient-module subgroup
normalizer contained in the original local image. Both orientations,
the degree-two rows, q=4 and n=2m remain unchanged.

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

/-- The full line quotient has the actual ambient centralizer, transporter
and subgroup-normalizer bounds on its nonzero orthogonal module. -/
theorem rankOne_unitary_short_quotient_centralizers
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
      let Q := ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∀ g, g*v*g⁻¹ ∈ Q → g ∈ X) ∧
      (∀ v ∈ V.map f, v ≠ 1 → centralizer ({v} : Set _) ≤ X) ∧
      ∀ P : Subgroup (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U),
        P ≤ V.map f → P ≠ ⊥ → normalizer (P : Set _) ≤ X := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_quotient_centralizers hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
