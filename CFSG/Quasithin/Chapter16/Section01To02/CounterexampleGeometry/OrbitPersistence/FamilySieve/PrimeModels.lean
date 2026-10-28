module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.SourceLists
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Sporadic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Preserving the odd-prime restriction in the source intersection

For a component with trivial two-core, (E2) forces any odd-prime PSL₂
parameter on the A.3.8 list to be Fermat or Mersenne. We reuse the proved
intrinsic comparisons with every characteristic-two model and every
sporadic carrier. The two source encodings of the characteristic-two list
are connected constructor by constructor, including the actual equivalence
between the local Ree construction and its canonical model. The overlaps
at five and seven and the original odd prime parameter are preserved.

Consequently only the J₁ comparison remains in the trivial-core branch.
Its exclusion is explicit in the conditional theorem below and is not
assumed to be a classification fact.

Source: Aschbacher–Smith, (E2) on p.1170 and the list intersection in
16.2.5 on p.1174, using A.3.8(3), p.45. The reused Chapter 15 lemmas
prove actual model comparisons independent of its counterexample setup.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
open ClassificationModels ChapterA.Section02
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
universe u
variable {S : Type u} [Group S]

private theorem evenTypeLieQuotient_transport {R : Type*} [Group R]
    (h : IsEvenTypeLieQuotient S) (e : R ≃* S) : IsEvenTypeLieQuotient R := by
  rcases h with h | ⟨f,h⟩ | ⟨n,hn,h⟩
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl ⟨f,h.of_mulEquiv e⟩)
  · exact Or.inr (Or.inr ⟨n,hn,h.of_mulEquiv e⟩)

private theorem lieTypeTwo_of_evenTypeLieQuotient (h : IsEvenTypeLieQuotient S) :
    LieTypeTwoModel S := by
  rcases h with h | ⟨f,h⟩ | h
  · exact Or.inl h
  · apply Or.inr ∘ Or.inl
    cases h with
    | linear hf iso => exact .linear f hf iso
    | symplectic hf iso => exact .symplectic f hf iso
    | g2 hf iso => exact .g2 f hf iso
    | triality hf iso => exact .triality f hf iso
    | ree_f4 m hm _ iso =>
      exact .ree m hm ((ReeF4.exists_localBlockInput_mulEquiv_iff S m).mpr iso)
    | symplectic_derived _ iso => exact .symplectic_derived iso
    | g2_derived _ iso => exact .g2_derived iso
    | tits _ iso => exact .tits iso
  · exact Or.inr (Or.inr h)

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hh : 2 ≤ 2^(2^k) := Nat.le_pow (by positivity)
    omega
  · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
    have hh := dvd_pow_self 2 hk0
    rw [← hk] at hh
    norm_num at hh

/-- All comparisons needed to preserve the odd-prime restriction of (E2). -/
theorem prime_parameter_of_evenType [Finite S] {p : ℕ}
    (hp : p.Prime) (hlarge : 3 < p) (hc : pCore 2 S = ⊥)
    (hm : ClassicalGroup.IsPSL S 2 p) (heven : IsEvenTypeComponent S) :
    IsFermatOrMersennePrime p := by
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hp5 : 5 ≤ p := by
    by_contra h
    have he : p = 4 := by omega
    subst p
    norm_num at hp
  let e : S ≃* (S ⧸ pCore 2 S) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
  rcases heven with hlie | h3 | ⟨q,hq,hqm⟩ | ⟨name,hn,_,hiso⟩
  · exact lie_odd_parameter hp ho hp5 hm
      (lieTypeTwo_of_evenTypeLieQuotient (evenTypeLieQuotient_transport hlie.1 e))
  · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h3
    have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [← Nat.card_congr a.toEquiv, hF] at hcard
    norm_num [Fin.prod_univ_succ] at hcard
    exact (psl_two_card_ne_5616 hm (by omega)).elim
  · have hparam := odd_parameter_unique ho (fermat_mersenne_odd hq) hm hqm
    exact hparam ▸ hq
  · obtain ⟨a⟩ := hiso
    exact (sporadic_separation_of_four sporadic_four_separation name hn
      (Or.inr ⟨hp,ho⟩) (hm.of_mulEquiv (e.trans a).symm)).elim

/-- The simple-list intersection, conditional only on excluding the actual J₁ carrier. -/
theorem simple_intersection_of_janko_exclusion [Finite S]
    (hj : ∀ (R : Type u) [Group R] [Finite R], pCore 2 R = ⊥ →
      IsEvenTypeComponent R → Nonempty (R ≃* Janko1.Model) → False)
    (hc : pCore 2 S = ⊥) (heven : IsEvenTypeComponent S) (hm : SourceOrbitModel S) :
    RankOneComponentModel S := by
  cases hm with
  | linear_even n hn iso => exact .linear_even n hn iso
  | suzuki m hm iso => exact .suzuki m hm iso
  | janko_one iso => exact (hj S hc heven iso).elim
  | linear_odd p hp hlarge iso =>
    have hprime := prime_parameter_of_evenType hp hlarge hc iso heven
    exact .linear_odd p hprime (by
      have ho := hp.odd_of_ne_two (by omega : p ≠ 2)
      obtain ⟨k,hk⟩ := ho
      omega) iso
end CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
end
