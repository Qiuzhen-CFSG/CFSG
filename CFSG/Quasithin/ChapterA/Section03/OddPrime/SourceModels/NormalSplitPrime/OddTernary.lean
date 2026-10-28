module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.OddLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.OddUnitary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary

/-!
# Odd-prime ternary rows on the original C-component

Pass through the literal ambient two-core quotient, preserving the whole
intrinsic component, rank, outside actor and split generation. The linear
and unitary row theorems then give the complete projective alternative.
The coprime-kernel star equivalences transfer both its component image and
its residual to the original H/O_{p′}(H). The p-prime-center hypothesis
is explicit and does not discard the nontrivial cubic-center branch.

Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Subgroup Theory.GroupTheory

/-- The two prime-field ternary rows, with their actual central-quotient markings.
The p-prime center includes a cubic cover whenever p is not three. -/
def OddTernaryModel (B : Type*) [Group B] (p : ℕ) : Prop :=
  Nat.Coprime p (Nat.card (center B)) ∧ ∃ r : ℕ, r.Prime ∧ Odd r ∧
    (ClassicalGroup.IsPSL (B ⧸ center B) 3 r ∨
      ClassicalGroup.IsPSU (B ⧸ center B) 3 r)

theorem OddTernaryModel.of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (h : OddTernaryModel B p) (e : A ≃* B) : OddTernaryModel A p := by
  obtain ⟨hz, r, hr, ho, hm⟩ := h
  refine ⟨?_, r, hr, ho, ?_⟩
  · rwa [Nat.card_congr (centerCongr e).toEquiv]
  · exact hm.imp (fun h => h.of_mulEquiv (centralQuotientEquiv e))
      (fun h => h.of_mulEquiv (centralQuotientEquiv e))

theorem alternatives_of_odd_ternary_model
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hm : OddTernaryModel (K ⧸ pCore 2 K) p)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  obtain ⟨hz, r, hprime, hodd, hm⟩ := hm.of_mulEquiv (twoCoreComponentEquiv hK)
  let f := QuotientGroup.mk' (pCore 2 H)
  have hc : Nat.Coprime p (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (Nat.coprime_two_right.mpr ho).pow_right m
  have hra : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  rcases hm with hlin | huni
  · obtain ⟨hp3, hcong, hmodel, hpgl⟩ := ordinary_odd_linear_projective (twoCore_sqtk hH)
      hp ho hra hz hprime hodd hlin (f a) ha'.1 ha'.2 (twoCore_join a hgen)
    apply Or.inr ∘ Or.inl
    refine ⟨hp3, false, r, hcong,
      hmodel.of_mulEquiv (starComponentEquiv p f (QuotientGroup.mk'_surjective _) hc K),
      Or.inl ?_⟩
    cases hp3
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpgl
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(starResidualEquiv 3 f (QuotientGroup.mk'_surjective _) hc).trans e⟩⟩
  · obtain ⟨hp3, hcong, hmodel, hpgu⟩ := ordinary_odd_unitary_projective (twoCore_sqtk hH)
      hp ho hra hz hprime hodd huni (f a) ha'.1 ha'.2 (twoCore_join a hgen)
    apply Or.inr ∘ Or.inl
    refine ⟨hp3, true, r, hcong,
      hmodel.of_mulEquiv (starComponentEquiv p f (QuotientGroup.mk'_surjective _) hc K),
      Or.inl ?_⟩
    cases hp3
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hpgu
    exact ⟨F, inferInstance, inferInstance, J, hF, hconj,
      ⟨(starResidualEquiv 3 f (QuotientGroup.mk'_surjective _) hc).trans e⟩⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
