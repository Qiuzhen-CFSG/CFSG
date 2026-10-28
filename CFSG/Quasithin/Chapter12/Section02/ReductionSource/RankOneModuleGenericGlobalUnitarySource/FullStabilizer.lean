module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FullStabilizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The original chosen module and full local long-root orbit

Apply the prepared theorem with the whole reduced module and the original
KnownSimple hypotheses. The same roots and full-line quotient have the
q²−1 full local orbit, exact centralizer preimage, and an ambient Sylow
centralizing the marked long root. Its quotient Sylow centralizes the
surviving image. Both orientations, degree-two rows and q=4 are retained.

Source: Aschbacher–Smith F.4.42 and 5.3/12.2, pp.295–296,659,795.
Ambient unique fixed cosets and the remaining F.4.42–43 arguments are
still separate obligations of the unconditional source producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal chosen-module input supplies full local orbit invariance,
exact quotient centralizers and an ambient Sylow centralizing the same long root. -/
theorem rankOne_unitary_short_full_stabilizer_orbit
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
      let X := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G))
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      (∀ g ∈ normalizer (L : Set G), g*t.val*g⁻¹ = t.val →
        ∃ a : centralizer ({t} : Set L),
          a.val.val*z.val.val*a.val.val⁻¹ = g*z.val.val*g⁻¹) ∧
      Nat.card {x : X // IsConj
        (⟨UnitarySource.shortCentralizerEmbedding L t z,L.le_normalizer z.val.property⟩ : X) x}
          = (2^m)^2 - 1 ∧
      (centralizer ({f z} : Set _)).comap
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) =
          centralizer ({UnitarySource.shortLineNormalizerMap L t U hU z} : Set _) ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _) ≤ X ∧
        (P : Subgroup _) ≤ centralizer ({UnitarySource.shortCentralizerEmbedding L t z} : Set _) ∧
        (P : Subgroup _) ≤ UnitarySource.shortLineNormalizer L t U ∧
      ∃ Pbar : Sylow 2 (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U),
        (Pbar : Subgroup _) =
          ((P : Subgroup _).subgroupOf (UnitarySource.shortLineNormalizer L t U)).map
            (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) ∧
        (Pbar : Subgroup _) ≤ centralizer ({f z} : Set _) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_full_stabilizer_orbit hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
