module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality

/-!
# Rudvalis has no permuting full Sylow pair at five

The checked odd-index maximal cover places a proper full Sylow product in one
of two actual Rudvalis maximal subgroups. Their orders are indivisible by 25.
Simplicity and perfectness are inherited from the original simple component.

Source: Aschbacher–Smith, Proposition 1.3.4, printed pp.510–511,
using the original full Sylow hypothesis in A.3.15.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd

private theorem rudvalis_twoCore_eq_bot [IsSimpleGroup Rudvalis.Model]
    [Group.IsPerfect Rudvalis.Model] : pCore 2 Rudvalis.Model = ⊥ := by
  rcases (inferInstance : (pCore 2 Rudvalis.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hs : Group.IsSolvable (pCore 2 Rudvalis.Model) := by
      let : Group.IsNilpotent (pCore 2 Rudvalis.Model) := pCore_isPGroup.isNilpotent
      infer_instance
    rw [h] at hs
    let := hs
    have hsol := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup Rudvalis.Model) ≃* Rudvalis.Model).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup Rudvalis.Model) ≃* Rudvalis.Model).surjective
    exact (Group.IsPerfect.not_isSolvable Rudvalis.Model hsol).elim

theorem rudvalis_no_five_pair [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
    (B : Subgroup Rudvalis.Model) (S : Sylow 2 Rudvalis.Model)
    (hB : XiOddQuotient 5 B)
    (hperm : (B : Set Rudvalis.Model) * (S : Set Rudvalis.Model) =
      (S : Set Rudvalis.Model) * (B : Set Rudvalis.Model)) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨M,hM,hodd,_,_,h25⟩ := exists_oddIndex_maximal_with_prime_square B S hB.isPGroup
    (by decide : 5 ≠ 2) (prime_square_dvd_complement hB) hperm
    (Group.IsPerfect.not_isSolvable Rudvalis.Model)
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover
    rudvalis_twoCore_eq_bot
    InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  rcases hcover M hM hodd with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Rudvalis.SylowOvergroups.max4_card] at h25
    norm_num at h25
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Rudvalis.SylowOvergroups.max6_card] at h25
    norm_num at h25

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J] {D B : Subgroup J} {S : Sylow 2 J}

theorem not_rudvalis [Group.IsPerfect D]
    (hA : OddCartan.AmbientInput κ D B S 5)
    (hB : SourceTransport.PairAction 5 (S : Subgroup J) B)
    (e : D ≃* Rudvalis.Model) : False := by
  let : D.Normal := hA.normal
  let : IsSimpleGroup D := hA.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact rudvalis_no_five_pair _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
