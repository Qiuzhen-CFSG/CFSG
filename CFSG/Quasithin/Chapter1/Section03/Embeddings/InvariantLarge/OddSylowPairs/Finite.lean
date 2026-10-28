module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs.FinitePrimes
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource

/-!
# Exceptional finite exclusions for the actual odd-complement Sylow pair

Certified carrier orders select the only possible large prime. The original
full pair then transports through the given model isomorphism to the proved
local exclusions for J₂, J₄, HS, Held, Rudvalis, Tits and binary triality.
Only inherited simplicity and perfectness are used where required; this
module does not assert them for the standalone model constructions.
Chapter13 applies these results to the actual ordinary two-core quotient.

Source: Aschbacher–Smith, 1.3.4, pp.510–511; 13.1.12(3), p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
open A315Source.ExceptionalOdd ClassificationModels
variable {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

/-- The actual jankoTwo pair is excluded at its forced prime. -/
theorem not_jankoTwo (h : HasOddSylowPair p A) (hp : 3 < p)
    (e : A ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have he := h.prime_eq_five_of_jankoTwo hp e
  subst p
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact jankoTwo_no_five_pair B S hB hperm

/-- The actual jankoFour pair is excluded at its forced prime. -/
theorem not_jankoFour (h : HasOddSylowPair p A) (hp : 3 < p)
    (e : A ≃* Janko4.Model) : False := by
  have he := h.prime_eq_eleven_of_jankoFour hp e
  subst p
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact jankoFour_no_eleven_pair B S hB hperm

/-- The actual higmanSims pair is excluded at its forced prime. -/
theorem not_higmanSims (h : HasOddSylowPair p A) (hp : 3 < p)
    (e : A ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have he := h.prime_eq_five_of_higmanSims hp e
  subst p
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact higmanSims_no_five_pair B S hB hperm

/-- The actual Held pair is excluded at both possible large primes. -/
theorem not_held (h : HasOddSylowPair p A) (hp : 3 < p)
    (e : A ≃* Held.He) : False := by
  have he := h.prime_five_or_seven_of_held hp e
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact held_no_pair he B S hB hperm

/-- Rudvalis inherits simplicity and perfectness from the original component. -/
theorem not_rudvalis [IsSimpleGroup A] [Group.IsPerfect A]
    (h : HasOddSylowPair p A) (hp : 3 < p) (e : A ≃* Rudvalis.Model) : False := by
  have he := h.prime_eq_five_of_rudvalis hp e
  subst p
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact rudvalis_no_five_pair B S hB hperm

/-- The Tits pair transports through the actual finite-image comparison. -/
theorem not_tits [IsSimpleGroup A] [Group.IsPerfect A]
    (h : HasOddSylowPair p A) (hp : 3 < p) (e : A ≃* Tits.ParrottGroup) : False := by
  have he := h.prime_eq_five_of_tits hp e
  subst p
  let f := e.trans Tits.parrottFiniteImageEquiv
  let : IsSimpleGroup Tits.Atlas1600Group := f.symm.isSimpleGroup
  let : Group.IsPerfect Tits.Atlas1600Group := Group.IsPerfect.ofSurjective
    (f := f.toMonoidHom) f.surjective
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv f
  exact tits_no_five_pair (Group.IsPerfect.not_isSolvable Tits.Atlas1600Group) B S hB hperm

/-- Binary triality is excluded through its genuine fixed model equivalence. -/
theorem not_triality_two (h : HasOddSylowPair p A) (hp : 3 < p)
    (hm : Triality.Standard.IsTrialityGroupAt 2 A) : False := by
  have he := h.prime_eq_seven_of_triality hp hm
  subst p
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff A).mp hm
  obtain ⟨S,B,hB,hperm⟩ := h.of_mulEquiv e
  exact triality_two_no_seven_pair B S hB hperm

/-- Every sporadic row permitted by the marked 1.1.5 catalogue is excluded. -/
theorem not_sporadic [IsSimpleGroup A] [Group.IsPerfect A]
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (name : SporadicName) (hn : name ≠ .j3) (he : Nonempty (A ≃* name.Carrier)) : False := by
  cases name with
  | m11 => exact h.not_mathieu hp .m11 (by simp) he
  | m12 => exact h.not_mathieu hp .m12 (by simp) he
  | m22 => exact h.not_mathieu hp .m22 (by simp) he
  | m23 => exact h.not_mathieu hp .m23 (by simp) he
  | m24 => exact h.not_mathieu hp .m24 (by simp) he
  | j2 => exact h.not_jankoTwo hp he.some
  | j3 => exact hn rfl
  | j4 => exact h.not_jankoFour hp he.some
  | hs => exact h.not_higmanSims hp he.some
  | he => exact h.not_held hp he.some
  | ru => exact h.not_rudvalis hp he.some

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
