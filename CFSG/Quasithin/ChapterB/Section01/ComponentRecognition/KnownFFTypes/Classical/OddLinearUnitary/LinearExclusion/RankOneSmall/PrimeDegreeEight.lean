module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.ModelBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CoverTransport
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.FourGroupGeneration
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.FixedSpaceCodimension

/-!
# The degree-eight reduction for PSL₂(13), PSL₂(17), PSL₂(19), PSL₂(23)

The source cubic actor has rank one or two, by faithful conjugation on the
actual prime-field central quotient. Its image in the automorphism group
has the same order. Four conjugates in rank one, or two conjugates in rank
two, give degree at most eight by intersecting their fixed spaces. The
conjugators lift through the specified cover, and every dimension is over
the original binary field.

The concrete cyclic and four-group generation theorems discharge both model
premises, including diagonal outer actors. This gives the unconditional source
degree bound and the strict ratio exclusions for 13, 19 and 23. At parameter
17 the degree is exactly eight; its module exclusion and the final six-parameter
assembly remain with their respective source owners.

Source: GM02, *Classification of 2F-modules I*, Proposition 4.1, manuscript
pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open PrimeDegreeEight

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem component_fixedSpace_eq_bot :
    fixedSpace ρ (generalizedFitting G) = ⊥ := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  exact fixedSpace_eq_bot_of_faithful_irreducible_on ρ _ h.faithful h.irreducible

omit [Finite G] in
private theorem degree_le_actor_conjugates (A : Subgroup G) {n : ℕ}
    (c : Fin n → G) (hc : generalizedFitting G ≤
      ⨆ i, A.map (MulAut.conj (c i)).toMonoidHom) :
    Module.finrank (ZMod 2) V ≤ n * fixedCodim ρ A := by
  let X (i : Fin n) := A.map (MulAut.conj (c i)).toMonoidHom
  have hz : fixedSpace ρ (⨆ i, X i) = ⊥ := by
    apply le_bot_iff.mp
    rw [← component_fixedSpace_eq_bot ρ h]
    exact ρ.invariants_comp_subtype_antitone hc
  have he : fixedSpace ρ (⨆ i, X i) = ⨅ i, fixedSpace ρ (X i) :=
    ρ.invariants_comp_iSup X
  have hd := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (X i))
  rw [← he, hz, Submodule.finrank_quotient] at hd
  simp only [finrank_bot, Nat.sub_zero] at hd
  change Module.finrank (ZMod 2) V ≤ ∑ i, fixedCodim ρ (X i) at hd
  simpa only [X, fixedCodim_map_conj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using hd

/-- The full source degree-eight implication, with precisely the two concrete
model-generation premises still to be discharged. No absolute irreducibility,
containment of the actor in the component, or field-size conclusion is used. -/
theorem source_degree_eight_of_model_generation
    (hcyclic : CyclicModelGeneration) (hfour : FourGroupModelGeneration)
    {q : ℕ} (hq : q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q)
    (hratio : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 8 := by
  have hp : q.Prime := by rcases hq with rfl | rfl | rfl | rfl <;> decide
  have ho : Odd q := by rcases hq with rfl | rfl | rfl | rfl <;> decide
  have hlarge : 4 ≤ q := by rcases hq with rfl | rfl | rfl | rfl <;> decide
  have hr : primeRank 2 G ≤ 2 := by
    simpa only [pow_one, ite_true] using
      source_two_rank_pslTwo ρ h hp ho (Or.inl rfl : 1 = 1 ∨ 1 = 2)
        (by simpa only [pow_one] using hlarge) (by simpa only [pow_one] using hm)
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hratio
  let : IsElementaryAbelian 2 A := hA.2
  have hrA := rank_le_of_primeRank_le hA hr
  have hpos := hA.rank_pos
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let f := quotientAction e
  have himage : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (A.map f) = 2 ^ rank A :=
    (source_elementary_image_card ρ h e A).trans hA.card_eq_two_pow_rank
  have hcases : rank A = 1 ∨ rank A = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨c, hc⟩ := hcyclic F q hq hF (A.map f) himage (by simpa [h1] using hcard)
    obtain ⟨d, hd⟩ := source_lift_actor_generation ρ h e A c hc
    have hdim := degree_le_actor_conjugates ρ h A d hd
    rw [h1] at hsmall
    omega
  · obtain ⟨c, hc⟩ := hfour F q hq hF (A.map f) himage (by simpa [h2] using hcard)
    obtain ⟨d, hd⟩ := source_lift_actor_generation ρ h e A c hc
    have hdim := degree_le_actor_conjugates ρ h A d hd
    rw [h2] at hsmall
    omega

/-- Literal consumer application: the degree-eight calculation excludes the
parameters whose checked binary degree minimum is greater than eight. -/
theorem source_prime_exclusion_of_model_generation
    (hcyclic : CyclicModelGeneration) (hfour : FourGroupModelGeneration)
    {q : ℕ} (hq : q = 13 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q) :
    2 < cubicRatio ρ := by
  apply source_exclusion_of_degree_eight ρ h hq hm
  exact source_degree_eight_of_model_generation ρ h hcyclic hfour
    (by rcases hq with rfl | rfl | rfl <;> simp) hm

/-- The remaining parameter 17 has exactly degree eight under the same
model-generation premises. Its module exclusion has a separate source owner. -/
theorem source_seventeen_degree_eq_eight_of_model_generation
    (hcyclic : CyclicModelGeneration) (hfour : FourGroupModelGeneration)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hratio : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V = 8 := by
  exact Nat.le_antisymm
    (source_degree_eight_of_model_generation ρ h hcyclic hfour (by simp) hm hratio)
    (eight_le_degree_seventeen ρ h.faithful hm)

/-- The source degree-eight bound at the four small prime parameters, with
both model-generation calculations discharged. The action remains over the
original binary field and the actor may include diagonal outer elements. -/
theorem source_degree_eight
    {q : ℕ} (hq : q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q)
    (hratio : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 8 :=
  source_degree_eight_of_model_generation ρ h
    cyclicModelGeneration fourGroupModelGeneration hq hm hratio

/-- The completed small-prime degree calculation rules out parameters 13, 19
and 23 at cubic ratio at most two, using their faithful binary degree minima. -/
theorem source_prime_exclusion
    {q : ℕ} (hq : q = 13 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q) :
    2 < cubicRatio ρ :=
  source_prime_exclusion_of_model_generation ρ h
    cyclicModelGeneration fourGroupModelGeneration hq hm

/-- Parameter 17 has binary degree exactly eight at cubic ratio at most two.
This supplies the degree input to the independent parameter-17 module exclusion. -/
theorem source_seventeen_degree_eq_eight
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hratio : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V = 8 :=
  source_seventeen_degree_eq_eight_of_model_generation ρ h
    cyclicModelGeneration fourGroupModelGeneration hm hratio

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
