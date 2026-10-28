module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.Contracts
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.ExceptionalG2
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# Reducing the complete C.2.7 alternatives on the selected component

The source theorem is applied to the actual relative component in H. Each
quotient comparison uses its canonical identification with the original
component quotient. The surviving natural module is transported through the
inclusion equivalence, so the component, exchanger and product remain those
selected before the classification. C.1.34 excludes the full SL₃ branch.

The local radical hypothesis is discharged by `SourceAssembly.LocalRadical`
in the final consumer. The universal earlier theorems retain their source
owners qt-c-02-offender-cases and qt-c01-rank-two.
Source: Aschbacher--Smith, C.2.7 and the exchanged case of 15.4.20, p.1164.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
universe u

/-- Intrinsic natural rank-one blocks transport with their actual module. -/
theorem l2Block_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {n : ℕ} (h : ChapterC.IsL2EvenBlock A n) :
    ChapterC.IsL2EvenBlock B n := by
  obtain ⟨hn, hs, F, hF, hfin, hc, hq, ρ, ⟨m⟩, hρ⟩ := h
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
  obtain ⟨m'⟩ := ChapterC.BlockModuleModel.exists_of_central_two_quotient
    e.toMonoidHom e.surjective hs.twoPerfect hp (hk ▸ bot_le) ρ m
  exact ⟨hn, ChapterC.RankOne.Solvable.isShort_of_equiv e hs, F, hF, hfin, hc,
    hq.of_mulEquiv (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)),
    ρ, ⟨m'⟩, hρ⟩

/-- The swapped models transport on the literal two-core quotient. -/
theorem swappedModel_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {p : ℕ} (h : Chapter1.XiEmbedding.SwappedModel p A) :
    Chapter1.XiEmbedding.SwappedModel p B := by
  rcases h with ⟨n, hn, hc, hm⟩ | ⟨q, hq, ho, hm⟩
  · exact Or.inl ⟨n, hn, hc, hm.of_mulEquiv e.symm⟩
  · exact Or.inr ⟨q, hq, ho, hm.of_mulEquiv e.symm⟩

variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- All eight C.2.7 alternatives reduce to the precise selected conclusion.
The only local premise is the independent consequence of C.2.2(3). -/
theorem selectedConclusion_of_local_radical
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))) :
    SelectedConclusion H U K K₁ r := by
  have hs := swappedModel_of_mulEquiv s.internalQuotientEquiv s.model
  let e := subgroupOfEquivOfLe s.component.1
  have hl2 : ∀ n, ChapterC.IsL2EvenBlock (K₁.subgroupOf H) n →
      ∃ n, Even n ∧ Nat.ModEq 3 (2 ^ n) 1 ∧ ChapterC.IsL2EvenBlock K₁ n := by
    intro n hb
    have hp := l2Block_parameter hb hs
    exact ⟨n, hp.1, hp.2, l2Block_of_mulEquiv e hb⟩
  have ha5 : ChapterC.IsAlternatingBlock (K₁.subgroupOf H) 5 →
      ChapterC.IsAlternatingBlock K₁ 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e
  have ha7 : ¬ ChapterC.IsAlternatingBlock (K₁.subgroupOf H) 7 := by
    intro hb
    have he := alternatingBlock_degree (by decide) (by decide) hb hs
    norm_num at he
  refine ⟨s, s.relative_subnormal, ?_⟩
  have cases := (c27 κ H _ _ _ hc).2.2
  cases cases with
  | chi _ cases =>
    cases cases with
    | rankOne n hb _ _ => exact Or.inl (hl2 n hb)
    | alternatingFive hb _ _ _ => exact Or.inr (ha5 hb)
    | alternatingSevenDihedral hb _ _ => exact (ha7 hb).elim
    | alternatingSevenElementary hb _ _ _ => exact (ha7 hb).elim
  | alternating n hlo hhi hb _ =>
    obtain rfl := alternatingBlock_degree hlo hhi hb hs
    exact Or.inr (ha5 hb)
  | ahatSix hb _ _ => exact (not_exceptionalAhat6Block hs hb).elim
  | exceptionalSeven hb _ => exact (not_exceptionalA7Block hs hb).elim
  | symplectic hb _ =>
    rcases hb with hb | hb
    · have he := alternatingBlock_degree (by decide) (by decide) hb hs
      norm_num at he
    · exact (not_sp4FourBlock hs hb).elim
  | gTwo hb _ => exact (not_binaryG2Derived_quotient hs hb.quotient_iso).elim
  | linearThree branch =>
    exact (SL3Geometry.not_source_SL3Branch_of_local_radical c134 h s κ hc branch hr).elim
  | linearHigher n hn hm _ =>
    exact (not_binaryLinear_quotient hn s.model (hm.of_mulEquiv
      (SL3Geometry.source_componentStarEquiv h s hc.normalized hr))).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
