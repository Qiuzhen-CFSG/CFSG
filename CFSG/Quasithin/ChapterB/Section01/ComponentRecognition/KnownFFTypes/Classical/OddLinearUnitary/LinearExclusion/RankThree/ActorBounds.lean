module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.Reduction
public import Theory.SpecificGroups.PSL3.OddPrimeActorRank
public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Defs
public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Inner
public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Graph
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Actor bounds for the odd-prime linear-three branch of K.2

The two-rank bound three is unconditional under the source hypotheses. It
uses the actual quotient L/Z(L) and the proved automorphism-rank bound.

The generation assembly lifts inner conjugators from that quotient to L,
then removes the central kernel by perfectness. It therefore contains the
whole original L, including its center, and treats graph outer involutions.
The explicit inner and graph matrix-generation calculations discharge both
model premises, giving three conjugates for every nonidentity involution.

The actual source degree application uses `source_degree_le_six_rank` and
gives binary degree at most eighteen when the cubic ratio is at most two.
Source: Guralnick–Malle, *Classification of 2F-modules I*, (2.6) and
Proposition 4.2, manuscript pp.4 and 9–10; Aschbacher–Smith K.2, p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeConjugateBounds

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [FiniteDimensional (ZMod 2) V] in
/-- The source actor has two-rank at most three, including covers and graph actions. -/
theorem source_two_rank_pslThree {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    primeRank 2 G ≤ 3 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact (primeRank_le_central_quotient_automorphisms_of_irreducible ρ
    (generalizedFitting G) h.faithful e).trans
      (Matrix.PSL3.OddPrimeActorRank.automorphism_two_rank
        (Group.IsPerfect.not_isSolvable _) hp ho hF)

omit [FiniteDimensional (ZMod 2) V] in
/-- Quotient model conjugators lift to the original group without losing the center. -/
theorem source_conjugates_of_projective_bound
    {S : Type*} [Group S]
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* S)
    (hgen : ∀ a : MulAut S, a ≠ 1 → a ^ 2 = 1 → MulAut.HasInnerConjugateCover a 3) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let f := MulAut.centralQuotientConjugation L e
  intro t ht ht2
  have hft : f t ≠ 1 := by
    intro he
    apply ht
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L h.faithful ht2
    rw [← MulAut.centralQuotientConjugation_ker L e]
    exact he
  obtain ⟨s, hs⟩ := hgen (f t) hft (by rw [← map_pow, ht2, map_one])
  exact MulAut.lift_conjugate_generation L e
    (centralizer_generalizedFitting_le G) t s hs

omit [FiniteDimensional (ZMod 2) V] in
/-- Conditional assembly of both concrete involution branches in the actual actor. -/
theorem source_three_conjugates_of_model_bounds
    (hi : InnerThreeBound.{0}) (hg : GraphThreeBound.{0})
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact source_conjugates_of_projective_bound ρ h e
    (three_bound_of_inner_graph hi hg (Group.IsPerfect.not_isSolvable _) hp ho hF)

/-- GM02 (2.6) gives binary degree at most eighteen once the two model bounds are supplied. -/
theorem source_degree_le_eighteen_of_model_bounds
    (hi : InnerThreeBound.{0}) (hg : GraphThreeBound.{0})
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (hq : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 18 := by
  have hd := source_degree_le_six_rank ρ h
    (source_three_conjugates_of_model_bounds ρ h hi hg hp ho hm) hq
  have hr := source_two_rank_pslThree ρ h hp ho hm
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Every source involution has three conjugates generating a subgroup containing
the whole original quasisimple subgroup, including its center. -/
theorem source_three_conjugates_pslThree
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin 3 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  exact source_three_conjugates_of_model_bounds ρ h
    inner_three_bound graph_three_bound hp ho hm

/-- The actual binary source representation has degree at most eighteen at
cubic ratio at most two; no model-generation premise remains. -/
theorem source_degree_le_eighteen_pslThree
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (hq : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 18 := by
  have hd := source_degree_le_six_rank ρ h
    (source_three_conjugates_pslThree ρ h hp ho hm) hq
  have hr := source_two_rank_pslThree ρ h hp ho hm
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
