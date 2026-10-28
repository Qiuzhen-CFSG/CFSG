module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.OddTernary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Covers
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Exclusions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.BinaryComponentResidual

/-!
# The remaining source rows after the odd ternary alternatives

The genuine Theorem C catalogue and checked outer automorphisms eliminate
all alternating, odd PSL₂, higher binary linear and sporadic rows when the
ordinary component has p-prime center. The complete odd-prime ternary
source alternatives leave only the actual characteristic-two Lie models.
The A.3.6 center classification separates the other case: p = 3, center
of order three, and a classical ternary cover or the Mathieu triple cover.
The alternating triple covers are excluded by the actual outside cubic.

This is a reduction on the original split domain, not the missing
classification of the remaining field, mixed and cubic-cover actors.
Source: Aschbacher–Smith A.3.6 and A.3.18, printed pp.43–45,51–53.
The outer-row proofs reuse the model calculations also used by the
nonblock sieve, without its stronger source-specific hypotheses.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
private theorem alternating_outer_two (m : ℕ) (hm : 5 ≤ m) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin m))) := by
  by_cases he : m = 6
  · subst m
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin m)
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card (Equiv.Perm (Fin m) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hc).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm he).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

private theorem two_transfer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsPGroup 2 (MulAut.Outer B)) : IsPGroup 2 (MulAut.Outer A) :=
  h.of_equiv (MulAut.outerCongr e).symm

private theorem sporadic_outer_two {J : Type*} [Group J] [IsSimpleGroup J]
    (hm : ChapterA.Section02.IsTheoremCSporadicModel J) : IsPGroup 2 (MulAut.Outer J) := by
  rcases hm with ⟨name, hne, ⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact two_transfer e Sporadic.Mathieu.m11_outer_isPGroup_two
    | m12 => exact two_transfer e (m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two)
    | m22 => exact two_transfer e (m22_outer_isPGroup_two_of_coverage
        Sporadic.Mathieu.m22DesignAutToAut_surjective)
    | m23 => exact two_transfer e Sporadic.Mathieu.m23_outer_isTwoGroup
    | m24 => exact two_transfer e Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
    | j2 => exact two_transfer e JankoTwo.outer_isPGroup_two
    | hs => exact two_transfer e (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
    | ru =>
      let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
      let := rudvalis_outer_subsingleton
      have ho : IsPGroup 2 (MulAut.Outer Rudvalis.Model) := IsPGroup.of_subsingleton 2 _
      exact two_transfer e ho
    | j3 => exact (hne rfl).elim
    | he => exact two_transfer e (Subgroup.isPGroup_outer_of_normalizer
        Held.permutationGroup 2 Held.Realization.normalizer_surjective
        Held.isPGroup_permutationNormalizerQuotient)
    | j4 => exact two_transfer e Janko4.AdequateLocal.outer_isPGroup_two
  · obtain ⟨e⟩ := e
    let := Janko1.OuterCertificate.outer_subsingleton
    have ho : IsPGroup 2 (MulAut.Outer Janko1.Model) := IsPGroup.of_subsingleton 2 _
    exact two_transfer e ho

/-- The exact characteristic-two families still requiring actor analysis. -/
def EvenLieModel (S : Type*) [Group S] : Prop :=
  ClassificationModels.IsBenderModel S ∨ RankTwoTheoremC S

private theorem ternary_or_even_of_not_outer_two
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hm : Section02.IsTheoremCModel S) (hout : ¬ IsPGroup 2 (MulAut.Outer S)) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧
      (ClassicalGroup.IsPSL S 3 r ∨ ClassicalGroup.IsPSU S 3 r)) ∨ EvenLieModel S := by
  have hm := SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative S) hm
  cases hm with
  | alternating n hn he =>
    exact (hout (two_transfer he.some (alternating_outer_two n hn.1))).elim
  | linear_odd r k hp ho hk _ hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact (hout (two_transfer e
      (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho (by omega) hF))).elim
  | three_odd r hp ho unitary hm =>
    refine Or.inl ⟨r, hp, ho, ?_⟩
    cases unitary
    · exact Or.inl hm
    · exact Or.inr hm
  | rank_one hm => exact Or.inr (Or.inl hm)
  | rank_two hm => exact Or.inr (Or.inr hm)
  | binary_linear n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    let a := (e.trans (Atlas.fieldEquivPSL n eF)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n))
    exact (hout (two_transfer a (Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two hn))).elim
  | sporadic name hne he =>
    exact (hout (sporadic_outer_two (Or.inl ⟨name, hne, he⟩))).elim
  | janko_one he => exact (hout (sporadic_outer_two (Or.inr he))).elim

variable {H : Type*} [Group H] [Finite H]

/-- A p-prime center leaves only an even-characteristic actor case after the
full odd-prime ternary alternatives have been proved. -/
theorem alternatives_or_even_of_coprime_center
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := by
  let B := K ⧸ pCore 2 K
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hout : ¬ IsPGroup 2 (MulAut.Outer (B ⧸ center B)) := by
    intro h
    apply outer_not_twoGroup hH hK hp ho hr hz a ha haK
    exact h.of_injective (MulAut.centralQuotientOuter (MulEquiv.refl _))
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl _))
  have hm := (twoCore_central_quotient_model hH hK).of_mulEquiv
    (centralQuotientEquiv (twoCoreComponentEquiv hK).symm)
  rcases ternary_or_even_of_not_outer_two hm hout with ⟨r, hp', ho', hm⟩ | hm
  · exact Or.inl (alternatives_of_odd_ternary_model hH hK hp ho hr
      ⟨hz, r, hp', ho', hm⟩ a ha haK hgen)
  · exact Or.inr hm

/-- The source catalogue separates the unresolved even-characteristic action
from the nontrivial cubic-center branch; no model tag replaces an alternative. -/
theorem alternatives_or_even_or_cubic_center
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨
      (Nat.Coprime p (Nat.card (center (twoCoreComponent K))) ∧
        EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
      (p = 3 ∧ Nat.card (center (twoCoreComponent K)) = 3 ∧
        ((∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
          IsSLSign (twoCoreComponent K) unitary 3 q) ∨ IsM22Cover (twoCoreComponent K))) := by
  classical
  by_cases hz : Nat.Coprime p (Nat.card (center (twoCoreComponent K)))
  · have hz' : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) := by
      rwa [← Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
    rcases alternatives_or_even_of_coprime_center hH hK hp ho hr hz' a ha haK hgen with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hz, h⟩)
  · rcases twoCore_center_cases hH hK with hb | ⟨⟨ez⟩, hm⟩
    · exact (hz (by rw [hb, card_bot]; exact Nat.coprime_one_right p)).elim
    have hc : Nat.card (center (twoCoreComponent K)) = 3 :=
      (Nat.card_congr ez.toEquiv).trans (by simp)
    have hp3 : p = 3 := by
      have hd : p ∣ 3 := by
        rw [hc] at hz
        exact hp.coprime_iff_not_dvd.not.mp hz |> not_not.mp
      exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.ne_one
    refine Or.inr (Or.inr ⟨hp3, hc, ?_⟩)
    cases hm with
    | classical u q hq hm => exact Or.inl ⟨u, q, hq, hm⟩
    | mathieu hm => exact Or.inr hm
    | alternating_six hm =>
      have he := not_alternating_cover hH hK a (ha.trans hp3) haK
      obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hm
      exact (he (Or.inl ⟨inferInstance,
        ⟨(centerCongr (twoCoreComponentEquiv hK).symm).trans ez⟩,
        ⟨(centralQuotientEquiv (twoCoreComponentEquiv hK).symm).trans eq⟩⟩)).elim
    | alternating_seven hm =>
      have he := not_alternating_cover hH hK a (ha.trans hp3) haK
      obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hm
      exact (he (Or.inr ⟨inferInstance,
        ⟨(centerCongr (twoCoreComponentEquiv hK).symm).trans ez⟩,
        ⟨(centralQuotientEquiv (twoCoreComponentEquiv hK).symm).trans eq⟩⟩)).elim

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

