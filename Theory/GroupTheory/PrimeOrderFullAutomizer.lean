module

public import Theory.GroupTheory.NormalizerActionSurjective
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Fusion under the full automizer of a prime-order subgroup

If `|N(P):C(P)| = p - 1` for a subgroup of order `p`, the normalizer
realizes every automorphism of `P`. Every nonidentity element generates
`P`, so an automorphism, and hence ambient conjugation, carries any such
element to any other.

Source application: Fong (1967), printed p.75, cyclic five-block case.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] (P : Subgroup G) [Finite P]

/-- Full automizer fuses all nonidentity elements of a prime-order subgroup. -/
theorem isConj_of_prime_card_full_automizer {p : ℕ} [Fact p.Prime] (hP : Nat.card P = p)
    (hindex : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = p - 1)
    (u v : P) (hu : u ≠ 1) (hv : v ≠ 1) : IsConj (u : G) (v : G) := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  have ho (x : P) (hx : x ≠ 1) : orderOf x = p := by
    apply orderOf_eq_prime _ hx
    simpa only [hP] using pow_card_eq_one' (x := x)
  have hg (x : P) (hx : x ≠ 1) : ∀ y : P, y ∈ zpowers x := by
    have hz : zpowers x = ⊤ := by
      apply eq_top_of_card_eq
      rw [Nat.card_zpowers, ho x hx, hP]
    simp [hz]
  let e : MulAut P := mulEquivOfOrderOfEq (hg u hu) (hg v hv)
    ((ho u hu).trans (ho v hv).symm)
  obtain ⟨n, hn⟩ := P.normalizerMonoidHom_surjective_of_index_eq_card
    (by rw [IsCyclic.card_mulAut, hP, Nat.totient_prime Fact.out]; exact hindex) e
  have he : e u = v := mulEquivOfOrderOfEq_apply_gen _ _ _
  have hv' : (n : G) * (u : G) * (n : G)⁻¹ = (v : G) := by
    have hh := congrArg (fun f : MulAut P => (f u : G)) hn
    change (n : G) * (u : G) * (n : G)⁻¹ = (e u : G) at hh
    simpa only [he] using hh
  exact isConj_iff.mpr ⟨(n : G), hv'⟩

end Subgroup
