module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Statement
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Monster
public import Theory.SpecificGroups.Janko3.Model.ThreeRank.Elementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elementary
public import Theory.SpecificGroups.HaradaNorton.ProperAlternatingTwelve
public import Theory.SpecificGroups.Alternating.ThreeRank
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.ONanEmbedding
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.BabyMonsterSection

/-!
# Unconditional sporadic catalogue exclusions for I.1.3

The actual elementary subgroups in J₃ and McL, the embedded A₁₂ in HN,
and the proved O'Nan, Baby Monster, Co₃ and Monster local obstructions
exclude these seven full-catalogue constructors. Source finiteness and
nontriviality are transported when the carrier construction needs them.
No arbitrary quotient-rank monotonicity or A.2.15 induction input is used.

Source: Aschbacher--Smith A.2.19 and I.1.3, printed pp.41 and 407.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open Theory.GroupTheory
universe u
variable {S : Type u} [Group S] [Finite S]

private theorem not_sqt_of_rank {M : Type} [Group M] [Finite M]
    (e : S ≃* M) (hr : 2 < primeRank 3 M) : ¬ IsStronglyQuasithin S := by
  intro h
  have hb := h 3 (by decide) (by decide)
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective
  omega

/-- The actual elementary 27-subgroup excludes the J₃ model. -/
theorem not_sqt_j3 (e : S ≃* Sporadic.Janko3.Model) : ¬ IsStronglyQuasithin S :=
  not_sqt_of_rank e Sporadic.Janko3.j3_primeRank_three_ge

/-- The actual elementary 81-subgroup excludes the McL model. -/
theorem not_sqt_mcl (e : S ≃* Sporadic.LeechRelated.McL.Carrier) :
    ¬ IsStronglyQuasithin S :=
  not_sqt_of_rank e Sporadic.LeechRelated.McL.two_lt_primeRank_three

/-- The checked A₁₂ embedding excludes HN without ambient order certification. -/
theorem not_sqt_hn (e : S ≃* HaradaNorton.HN) : ¬ IsStronglyQuasithin S := by
  intro h
  let f := e.symm.toMonoidHom.comp HaradaNorton.OrderCertificate.alternatingTwelveEmbedding
  have hf : Function.Injective f :=
    e.symm.injective.comp HaradaNorton.OrderCertificate.alternatingTwelveEmbedding_injective
  have hr := alternatingGroup.ThreeRank.three_le_primeRank (n := 12) (by decide)
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hb := h 3 (by decide) (by decide)
  omega

/-- The O'Nan E₉ × A₄ subgroup supplies the required local obstruction. -/
theorem not_sqt_onan (e : S ≃* ONan.Model) : ¬ IsStronglyQuasithin S :=
  fun h => ChapterA.onan_not_quasithin (isQuasithin_of_equiv e h.quasithin)

/-- The actual A₉ subgroup in an involution centralizer excludes the Baby Monster. -/
theorem not_sqt_babyMonster [Nontrivial S] (e : S ≃* BabyMonster.Carrier) :
    ¬ IsStronglyQuasithin S :=
  fun h => ChapterA.not_quasithin_of_babyMonster_equiv e h.quasithin

/-- All seven completed exclusions as literal constructors of the full catalogue. -/
theorem sporadic_name_restrictions [Nontrivial S] (h : IsStronglyQuasithin S)
    {name : KnownSimple.SporadicName} (he : Nonempty (S ≃* name.Carrier)) :
    name ≠ .j3 ∧ name ≠ .mcl ∧ name ≠ .hn ∧ name ≠ .onan ∧
      name ≠ .babyMonster ∧ name ≠ .co3 ∧ name ≠ .monster := by
  obtain ⟨e⟩ := he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst name
  · exact not_sqt_j3 e h
  · exact not_sqt_mcl e h
  · exact not_sqt_hn e h
  · exact not_sqt_onan e h
  · exact not_sqt_babyMonster e h
  · exact RankFilters.Leech.co3_not_stronglyQuasithin_of_equiv e h
  · exact RankFilters.Monster.not_stronglyQuasithin_of_equiv e h

end CFSG.Quasithin.ChapterI.SQTKMultipliers
