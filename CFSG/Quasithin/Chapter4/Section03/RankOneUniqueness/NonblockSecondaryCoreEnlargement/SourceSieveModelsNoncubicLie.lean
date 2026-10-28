module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsNoncubic
public import Theory.SpecificGroups.SymplecticFour.NondefiningPrimeActors
public import Theory.SpecificGroups.G2.NoncubicFieldActors

/-!
This additive source variant uses `SecondaryActionData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# Symplectic and G₂ restrictions at noncubic source primes

The concrete binary symplectic and G₂ field-actor calculations absorb every
ambient p-element when the component has p-rank two. The literal source
torus has an order-p element outside the ordinary component in the ambient
two-core quotient. Applying those calculations there is a contradiction.
Consequently each of these full component quotients has rank one at every
noncubic torus prime. The model dispatch removes both rows while preserving
the remaining full covering center and actual model isomorphisms.

These results discharge two Lie-family branches of original 4.3.12(2).
The unitary, triality and Ree restrictions, cubic diagonal clause and the
4.3.16 local inspection remain with qt-d-1222-nonblock-endgame-sieve.
The source MSData and SecondaryActionData are supplied by the final contradiction
owner qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12–16, pp.617–618.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Every odd torus prime has rank one in a full binary symplectic quotient. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_binary_symplectic
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSp (s.component ⧸ pCore 2 s.component) 2 (2 ^ f)) :
    primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  have hz := SecondaryActionData.twoCoreComponent_center_eq_bot s a
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  have hZ : Nat.Coprime p (Nat.card (center (SecondaryActionData.twoCoreComponent s))) := by
    rw [hz]
    simp
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < f)
  have hrI : 2 ≤ primeRank p (SecondaryActionData.twoCoreComponent s) := by
    rw [primeRank_congr p (SecondaryActionData.twoCoreComponentEquiv s),
      primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,hr]
  have he := Theory.SpecificGroups.SymplecticFour.NondefiningPrimeActors.component_eq_primeClosure_and_residual
    (SecondaryActionData.twoCoreComponent_isComponent s) hlarge ho hZ hrI
    ((SecondaryActionData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho)
    (SecondaryActionData.twoCoreCentralModel s a
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
  exact ((SecondaryActionData.twoCoreComponent_ne_prime_closures s hp ho hd).2 he.2).elim

/-- A noncubic torus prime has rank one in the full binary G₂ quotient, including G₂(4). -/
theorem SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_g2
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At (s.component ⧸ pCore 2 s.component) (2 ^ f)) :
    primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hprime : 3 < p := by have hh := hp.two_le; omega
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < f)
  have hz := SecondaryActionData.twoCoreComponent_center_eq_bot s e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge)
  have hZ : Nat.Coprime p (Nat.card (center (SecondaryActionData.twoCoreComponent s))) := by
    rw [hz]
    simp
  have hrI : 2 ≤ primeRank p (SecondaryActionData.twoCoreComponent s) := by
    rw [primeRank_congr p (SecondaryActionData.twoCoreComponentEquiv s),
      primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,hr]
  have he := Atlas.G2.NoncubicFieldActors.component_eq_primeClosure_and_residual
    (SecondaryActionData.twoCoreComponent_isComponent s) hlarge hprime hZ hrI
    ((SecondaryActionData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho)
    (SecondaryActionData.twoCoreCentralModel s e
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge))
  exact ((SecondaryActionData.twoCoreComponent_ne_prime_closures s hp ho hd).2 he.2).elim

/-- At noncubic rank two only unitary, triality and Ree quotients remain,
including the full binary special-unitary three-cover. -/
theorem SecondaryActionData.noncubic_rank_two_remaining_models (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : 2 ≤ primeRank p s.component) :
    (center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ((∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) ∨
        (∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2 ^ f)
          (s.component ⧸ pCore 2 s.component)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At (s.component ⧸ pCore 2 s.component) m))) ∨
    (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
      ∃ f : ℕ, 1 ≤ f ∧ Odd f ∧ IsSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) := by
  rcases SecondaryActionData.noncubic_rank_two_refined_models s D h hp ho hd hp3 hr with
    ⟨hz, hm | hm | hm | hm | hm⟩ | hm
  · exact Or.inl ⟨hz, Or.inl hm⟩
  · obtain ⟨f,hf,hm⟩ := hm
    have he := SecondaryActionData.component_primeRank_eq_one_of_binary_symplectic s D h hp ho hd hf hm
    omega
  · obtain ⟨f,hf,hm⟩ := hm
    have he := SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_g2 s D h hp ho hd hp3 hf hm
    omega
  · exact Or.inl ⟨hz, Or.inr (Or.inl hm)⟩
  · exact Or.inl ⟨hz, Or.inr (Or.inr hm)⟩
  · exact Or.inr hm
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
