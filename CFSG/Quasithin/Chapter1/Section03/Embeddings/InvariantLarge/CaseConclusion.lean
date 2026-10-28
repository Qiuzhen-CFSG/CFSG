module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Exclusions

/-!
# Completing the invariant large-prime case split

Apply the original A.3.15 cases to the marked faithful section. The cyclic
rows contradict the intrinsic odd complement. The odd-characteristic Cartan
row contradicts its invariant cyclic factorization. Rank-one binary rows are
cyclic; G₂, triality and Ree give power actions; the linear binary row adds
only a single involution. Each contradicts actual Frattini irreducibility.

The defining linear row identifies its defining prime with p and lifts the
projective model to the whole cover. The symplectic row supplies the original
plane, cyclic automizer, even degree and field congruence, then lifts through
the proved trivial symplectic multiplier. Every concrete geometry and action
premise is discharged; only the earlier A.3.15 case list enters this step.

Source: Aschbacher–Smith Proposition 1.3.4, printed pp.510–511, p > 3 case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u v
variable {J : Type u} [Group J] [Finite J]
variable {D B : Subgroup J} [D.Normal] {S : Sylow 2 J} {p : ℕ}

/-- The original A.3.15 cases, after imposing the actual intrinsic action,
leave precisely the linear and symplectic alternatives on the whole cover. -/
theorem alternatives_of_A315_cases
    {Q : Type v} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : Q ⧸ center Q ≃* D)
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hC : centralizer (D : Set J) = ⊥)
    (hc : A315PrimeCases D B S p) :
    Nonempty (B ≃* Plane p) ∧
      (LinearThreeModel p Q ∨ (SymplecticModel p Q ∧ IsCyclic (automizer S B))) := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : IsSimpleGroup D := hA.simple
  let : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hna : ¬ IsMulCommutative D := Group.IsPerfect.not_isMulCommutative D
  cases hc with
  | cyclic hcyc => exact (hB.oddComplement.not_isCyclic hcyc).elim
  | definingThree q hq ho hm he =>
    obtain ⟨j⟩ := he
    have hcard : Nat.card B = q ^ 2 := by
      rw [Nat.card_congr j.toEquiv]
      change Nat.card (Fin 2 → ZMod q) = q ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hpB : p ∣ Nat.card B := hA.p_group.card_eq_or_dvd.resolve_left
      (by have hh := hB.oddComplement.one_lt_card hA.prime; omega)
    rw [hcard] at hpB
    have hpq := hA.prime.dvd_of_dvd_pow hpB
    have heq : p = q := (Nat.dvd_prime hq).mp hpq |>.resolve_left hA.prime.ne_one
    subst q
    refine ⟨⟨j⟩, Or.inl (linearThreeModel_of_central_quotient hA.prime hA.large ?_)⟩
    obtain ⟨F, _, _, hF, ⟨k⟩⟩ := hm
    exact ⟨F, inferInstance, inferInstance, hF, ⟨e.trans k⟩⟩
  | @oddCartan K q hq δ ε c =>
    obtain ⟨A, C, hAc, hCc, hgen, hn⟩ := c.invariant_factorization hA
    let _ := hAc
    let _ := hCc
    exact (hB.not_cyclic_factorization A C hgen hn).elim
  | rankOne n hn hm =>
    have hh := EvenActions.RankOne.isCyclic_of_generalizedFitting D hA.fitting hna
      hn hm hA.large S B hA.p_group hA.inside hA.permutes
    exact (hB.oddComplement.not_isCyclic hh).elim
  | @linear F hF hfin n c =>
    have hi : EvenActions.Linear.SourceAlignment.AmbientInput KnownSimple.IsKnownSimple D B S p :=
      ⟨hA.sqtk, hA.fitting, hA.simple, hna, hA.prime, hA.large, hA.p_group, hA.inside, hA.permutes⟩
    obtain ⟨g, hg, hp⟩ := EvenActions.Linear.frattini_of_source_configuration F hi c
    exact (hB.not_power_involution g hg hp).elim
  | @symplectic F hF hfin n c =>
    have hn := c.normalizes_ambient D B (S : Subgroup J) hA.inside
    obtain ⟨hplane, hcyc, hmod, heven⟩ := symplectic_alternative_of_normalizes
      c.field_card c.degree hA.large D c.model.symm S B hA.inside hC hn
      hB.oddComplement hB.commutator
    obtain ⟨j, _⟩ := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.exists_whole_model
      c.field_card c.degree (e.trans c.model)
    exact ⟨hplane, Or.inr ⟨⟨n, heven, hmod, F, inferInstance, inferInstance,
      c.field_card, ⟨j⟩⟩, hcyc⟩⟩
  | @g2 F hF eG n f F₀ H₀ I c =>
    exact (hB.not_power (EvenActions.G2.Source.frattini_power_of_source D c)).elim
  | triality a n eG c =>
    have hi : EvenActions.Triality.SourceAlignment.AmbientInput KnownSimple.IsKnownSimple D B S p :=
      ⟨hA.sqtk, hA.fitting, hA.simple, hna, hA.prime, hA.large, hA.p_group,
        hA.inside, hA.permutes, hA.three_residual⟩
    exact (hB.not_power (EvenActions.Triality.frattini_power_of_source hi a n eG c)).elim
  | ree m d eG n f F₀ H₀ I c =>
    exact (hB.not_power (EvenActions.Ree.Source.frattini_power_of_source D hA.fitting hna
      hA.large hA.p_group hA.inside c)).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
