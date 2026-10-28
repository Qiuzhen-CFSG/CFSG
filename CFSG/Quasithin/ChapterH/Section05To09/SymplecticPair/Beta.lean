module

public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Beta.Basic
public import Theory.Representation.SymplecticConjugatePair.OddOrder

/-!
# Inner actors and the pointwise-centralizer bridge for H.7

The explicit action restriction in `Setup` transports fixed spaces from the
embedded derived symplectic group. Its nonidentity odd-order elements
therefore have binary fixed codimension at least 4n. Separately, the actual
two-residual of a pointwise centralizer supplies an odd-prime actor, so a
bound for all such actors implies the source β condition for subspaces.

The SQTK local argument forcing small-displacement actors to be inner and
the binary strengthening to six are still required. The last theorem is
an explicit conditional bridge, not a completed proof of H.7.

Source: Aschbacher–Smith H.7, printed pp.388–389, with the definition of β
on p.377, combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open SymplecticConjugatePair SymplecticConjugatePair.OddOrder
open Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
variable {F M : Type*} [Field F] [Algebra (ZMod 2) F] [Group M]

/-- Transport through the specified intertwining equality preserves actual fixed spaces. -/
theorem Setup.fixedSpace_embedding (s : Setup F M) (g : commutator (Sp F)) :
    fixedSpace s.action (Subgroup.zpowers (s.embedding g)) =
      fixedSpace (binaryPair s.twist) (Subgroup.zpowers g.val) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff]
  have he := congrArg (fun ρ : Representation (ZMod 2) (commutator (Sp F)) (Space F) =>
    ρ g v) s.restriction
  change s.action (s.embedding g) v = binaryPair s.twist g.val v at he
  rw [he]

/-- The odd-order bound for actors in the actual embedded derived symplectic group. -/
theorem Setup.four_mul_le_fixedCodim_of_mem_range [Finite F] [CharP F 2]
    (s : Setup F M) {n : ℕ} (hF : Nat.card F = 2^n) {x : M}
    (hx : x ∈ s.embedding.range) (hne : x ≠ 1) (ho : Odd (orderOf x)) :
    4*n ≤ fixedCodim s.action (Subgroup.zpowers x) := by
  obtain ⟨g, rfl⟩ := hx
  have hg : g.val ≠ 1 := by
    intro he
    exact hne ((congrArg s.embedding (Subtype.ext he)).trans s.embedding.map_one)
  have hord : orderOf (s.embedding g) = orderOf g :=
    orderOf_injective s.embedding s.embedding_injective g
  have hgodd : Odd (orderOf g.val) := by rwa [Subgroup.orderOf_coe, ← hord]
  unfold fixedCodim
  rw [s.fixedSpace_embedding]
  exact four_mul_le_fixedCodim s.twist hg hgodd hF
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open SymplecticConjugatePair SymplecticConjugatePair.OddOrder
open Representation.BinaryOffender
variable {F M : Type*} [Field F] [Algebra (ZMod 2) F] [Group M]

/-- The source centralizer C_M(U), fixing every vector of U under the actual action. -/
def Setup.pointwiseCentralizer (s : Setup F M) (U : Submodule (ZMod 2) (Space F)) :
    Subgroup M := pointwiseFixer s.action U

theorem Setup.mem_pointwiseCentralizer (s : Setup F M) (U : Submodule (ZMod 2) (Space F))
    (x : M) : x ∈ s.pointwiseCentralizer U ↔ ∀ v ∈ U, s.action x v = v := Iff.rfl

/-- The finite-group bridge to the source β condition. This is conditional on
the actor bound; it does not assert that the remaining overgroup cases are proved. -/
theorem Setup.beta_condition_of_actor_bound [Finite F] [Finite M] (s : Setup F M) (b : ℕ)
    (hb : ∀ (p : ℕ) (x : M), p.Prime → Odd p → orderOf x = p →
      b ≤ fixedCodim s.action (Subgroup.zpowers x))
    (U : Submodule (ZMod 2) (Space F))
    (hU : pResidual 2 (s.pointwiseCentralizer U) ≠ ⊥) :
    b ≤ Module.finrank (ZMod 2) (Space F ⧸ U) :=
  codim_bound_of_odd_prime_actors s.action b hb U hU
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
