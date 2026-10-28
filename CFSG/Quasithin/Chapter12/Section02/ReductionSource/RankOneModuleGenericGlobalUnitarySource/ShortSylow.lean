module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The original chosen module and ambient short-centralizer Sylows

Apply the prepared construction with the original whole reduced module.
The local Sylow centralizing the marked long root extends to a Sylow of
C_G(t) inside N_G(L), with exact residual preimage. The same full short
line is normalized, and the resulting Sylow of its literal normalizer
quotient has the same residual preimage. Both orientations, degree-two
rows, q=4 and the entire q-element kernel are retained.

Source: Aschbacher–Smith F.4.42 and 5.3/12.2, pp.295–296,659,795.
The ambient Sylow need not yet centralize the marked long root; ambient
unique fixed cosets, maximal-W containment and order remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal chosen-module input supplies Sylows on the ambient short
centralizer and its full-line quotient, retaining the same marked roots. -/
theorem rankOne_unitary_short_quotient_ambient_sylow
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
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      U = V ⊓ center (centralizer ({t} : Set L)) ∧
      V.map (centralizer ({t} : Set L)).subtype =
        ⁅pCore 2 L,centralizer ({t} : Set L)⁆ ∧
      (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ≤
        UnitarySource.shortLineNormalizer L t U ∧
      ∃ R : Sylow 2 (centralizer ({t} : Set L)),
        (R : Subgroup _) ≤ centralizer ({z} : Set _) ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _).comap (UnitarySource.shortCentralizerEmbedding L t) = R ∧
        L.pCoreIn 2 ≤ (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ∧
        (P : Subgroup _).map (centralizer ({t.val} : Set G)).subtype ≤ normalizer (L : Set G) ∧
        (P : Subgroup _) ≤ UnitarySource.shortLineNormalizer L t U ∧
      ∃ Pbar : Sylow 2 (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U),
        (Pbar : Subgroup _) =
          ((P : Subgroup _).subgroupOf (UnitarySource.shortLineNormalizer L t U)).map
            (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) ∧
        (Pbar : Subgroup _).comap f = R := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_quotient_ambient_sylow hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
