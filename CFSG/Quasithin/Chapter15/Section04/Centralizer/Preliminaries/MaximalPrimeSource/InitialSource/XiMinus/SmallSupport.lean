module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Action
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.FrattiniPair
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.NoncyclicSupport

/-!
# Prime restriction and the first canonical five-factor in the Xi argument

Reducedness gives trivial two-core in the literal centralizer quotient.
Its odd core is self-centralizing, so an inclusion-minimal cubic actor at
the global minimum moves that core. The cyclic and noncyclic branches of
D.2.13 restrict the source prime to three or five. In the five case the
noncyclic branch first forces rank one, and the cyclic branch constructs
an actual order-five commutator of support dimension four in the canonical
D.2.12 family.

The final consumer closes the three branch of Xi-minus. The two generating
factors and their preservation by the full original normalizer remain to
be constructed; the conditional consumer does not claim those conclusions.

Source: Aschbacher–Smith, Lemma 3.2.13, printed pp.584–585, using D.2.13,
printed pp.184–185, and D.2.12, printed pp.183–184.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

/-- Every nontrivial elementary two-actor moves the actual odd core. -/
theorem source_oddCore_moved (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hp : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X))
    {A : Subgroup (sourceActionGroup hX)} (hA : IsElementaryTwo A) :
    ⁅pCore p (sourceActionGroup hX), A⁆ ≠ ⊥ := by
  let := sourceModule_normal hX
  have hc : centralizer (pCore p (sourceActionGroup hX) : Set (sourceActionGroup hX)) ≤
      pCore p (sourceActionGroup hX) :=
    centralizer_pCore_le_of_quotient_isPGroup p 2 hred.quotient_pCore_eq_bot
      (source_oddCore_quotient_isTwoGroup hX hT hp)
  intro he
  have hle : A ≤ pCore p (sourceActionGroup hX) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans hc
  have hdis : Disjoint A (pCore p (sourceActionGroup hX)) :=
    IsPGroup.disjoint_of_ne 2 p (by intro e; rw [← e] at ho; norm_num at ho)
      _ _ (by let := hA.2; exact IsElementaryAbelian.isPGroup 2 A) pCore_isPGroup
  exact hA.1 (bot_unique ((le_inf le_rfl hle).trans hdis.le_bot))

/-- The source prime is three or five, from an actual minimal cubic actor. -/
theorem source_prime_restriction (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hratio : cubicRatio (sourceRepresentation hX) ≤ 2)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hp : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X)) :
    p = 3 ∨ p = 5 := by
  let := sourceModule_normal hX
  let ρ := sourceRepresentation hX
  have hf : Function.Injective ρ :=
    Representation.NormalElementaryQuotient.representation_injective _ _ _ _
  obtain ⟨A, hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hratio
  have hm := source_oddCore_moved hX hT hred ho hp hA.1.2.1
  have hpos := hA.1.2.1.rank_pos
  by_cases hr : rank A = 1
  · exact (ChapterD.source_lemma_D_2_13_cyclic_prime ρ hf hA hr ho hm).1
  · exact Or.inl (ChapterD.source_lemma_D_2_13_noncyclic_prime ρ hf hA
      (by omega) ho hm)

/-- In the five case the actor has rank one; its literal commutator has
order five and support dimension four. Noncyclicity is excluded by D.2.13(5). -/
theorem source_five_support (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hratio : cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    ∃ A : Subgroup (sourceActionGroup hX),
      A ∈ ChapterD.QhatStar (sourceRepresentation hX) ∧ rank A = 1 ∧
      ⁅pCore 5 (sourceActionGroup hX), A⁆ ≠ ⊥ ∧
      Nat.card (⁅pCore 5 (sourceActionGroup hX), A⁆ : Subgroup _) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator (sourceRepresentation hX) ⊤
        ⁅pCore 5 (sourceActionGroup hX), A⁆) = 4 := by
  let := sourceModule_normal hX
  let ρ := sourceRepresentation hX
  have hf : Function.Injective ρ :=
    Representation.NormalElementaryQuotient.representation_injective _ _ _ _
  obtain ⟨A, hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hratio
  have hm := source_oddCore_moved hX hT hred (by decide : Odd 5) hp hA.1.2.1
  have hr : rank A = 1 := by
    have hpos := hA.1.2.1.rank_pos
    by_contra hn
    have he := ChapterD.source_lemma_D_2_13_noncyclic_prime ρ hf hA
      (by omega : 1 < rank A) (by decide : Odd 5) hm
    norm_num at he
  have hs := ChapterD.source_lemma_D_2_13_cyclic_five ρ hf hA hr hm
  exact ⟨A, hA, hr, hm, hs.2.1, hs.2.2.2.1⟩

/-- The literal canonical order-five, four-dimensional-support family. -/
def sourceFiveFactors (hX : X ∈ Chapter1.Xi G T) : Set (Subgroup (sourceActionGroup hX)) :=
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  ChapterD.smallSupportFactors (sourceActionGroup hX)
    (Multiplicative (Additive (sourceModule T X))) 2

/-- The D.2.13 commutator belongs to the actual canonical D.2.12 family
and lies in the original odd image. -/
theorem source_five_canonical_support (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hratio : cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    ∃ A : Subgroup (sourceActionGroup hX),
      A ∈ ChapterD.QhatStar (sourceRepresentation hX) ∧ rank A = 1 ∧
      ⁅pCore 5 (sourceActionGroup hX), A⁆ ≠ ⊥ ∧
      ⁅pCore 5 (sourceActionGroup hX), A⁆ ≤ sourceOddImage hX ∧
      ⁅pCore 5 (sourceActionGroup hX), A⁆ ∈ sourceFiveFactors hX := by
  obtain ⟨A, hA, hr, hn, hc, hd⟩ := source_five_support hX hT hred hratio hp
  refine ⟨A, hA, hr, hn, ?_, ?_⟩
  · rw [sourceOddImage_eq_pCore hX hT (by decide : Odd 5) hp]
    exact commutator_le_left _ _
  · let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
    refine ⟨(commutator_le_left _ _).trans (pCore_le_fitting _ 5), hc, ?_⟩
    rw [Representation.BinaryGroupAction.commutator_card, hd]

/-- The prime restriction closes the three branch of the original Xi-minus
consumer. Construction of the preserved pair remains explicit only in the five branch. -/
theorem source_mem_XiMinus_of_five_pair (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hratio : cubicRatio (sourceRepresentation hX) ≤ 2)
    (hpair : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X) →
      HasNormalizerFrattiniPair X) : X ∈ Chapter3.XiMinus G T := by
  obtain ⟨p, hp, ho, hq, hdiv⟩ := hX.card_prime_divisors
  let : Fact p.Prime := ⟨hp⟩
  rcases source_prime_restriction hX hT hred hratio ho hq with he | he
  · exact ⟨hX, Or.inl (by simpa only [he] using hdiv)⟩
  · subst p
    obtain ⟨B, C, hB, hC, hne, hgen, hperm⟩ := hpair hq
    exact source_mem_XiMinus_of_frattini_pair hX hq.isPGroup
      B C hB hC hne hgen hperm

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
