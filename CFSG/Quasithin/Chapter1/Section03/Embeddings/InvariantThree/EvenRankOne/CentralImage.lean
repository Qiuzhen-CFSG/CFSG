module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair

/-!
# A cyclic central image gives an invariant line

In the three-rank sieve, a cyclic image of the odd complement in Q/Z(Q)
already excludes irreducibility. Its kernel is central, so the complement
is abelian and hence is the elementary plane in Definition 1.3.1. The
intersection with Z(Q) is nontrivial by noncyclicity and proper by [Q,R]=Q.
Every extending automorphism preserves this intersection. Passing through
the trivial Frattini subgroup gives the required invariant line.

This argument applies to arbitrary central covers; it needs no multiplier
table or identification of a cover with its simple quotient.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed pp.510–511
(PDF pp.527–528), the Cartan and irreducibility sieve.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne

variable {Q : Type*} [Group Q]

/-- The actual image in the quotient by the whole center. -/
def centralImage (R : Subgroup Q) : Subgroup (Q ⧸ center Q) :=
  R.map (QuotientGroup.mk' (center Q))

/-- The center of the ambient group, intersected with the odd complement. -/
def centralTrace (R : Subgroup Q) : Subgroup R := (center Q).subgroupOf R

theorem centralTrace_le_center (R : Subgroup Q) : centralTrace R ≤ center R := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp hx y

theorem centralTrace_eq_ker (R : Subgroup Q) :
    centralTrace R = ((QuotientGroup.mk' (center Q)).subgroupMap R).ker := by
  ext x
  change (x : Q) ∈ center Q ↔ _
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : Q)).mpr hx
  · intro hx
    exact (QuotientGroup.eq_one_iff (x : Q)).mp (congrArg Subtype.val hx)

/-- A cyclic central image rules out the extraspecial alternative. -/
theorem elementary_of_cyclic_centralImage [Finite Q] (R : Subgroup Q)
    (hR : XiOddQuotient 3 R) (hc : IsCyclic (centralImage R)) :
    IsElementaryAbelian 3 R := by
  let _ : IsCyclic (R.map (QuotientGroup.mk' (center Q))) := hc
  let f := (QuotientGroup.mk' (center Q)).subgroupMap R
  let _ : IsMulCommutative R := f.isMulCommutative_of_isCyclic_of_ker_le_center
    ((centralTrace_eq_ker R) ▸ centralTrace_le_center R)
  rcases hR with ⟨he, _⟩ | ⟨he, _, _⟩
  · exact he
  · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
      (center_eq_top (G := R))).elim

theorem centralTrace_ne_bot [Finite Q] (R : Subgroup Q)
    (hR : XiOddQuotient 3 R) (hc : IsCyclic (centralImage R)) :
    centralTrace R ≠ ⊥ := by
  intro hb
  let _ : IsCyclic (R.map (QuotientGroup.mk' (center Q))) := hc
  apply hR.not_isCyclic
  apply isCyclic_of_injective ((QuotientGroup.mk' (center Q)).subgroupMap R)
  exact (MonoidHom.ker_eq_bot_iff _).mp ((centralTrace_eq_ker R).symm.trans hb)

theorem centralTrace_ne_top [Nontrivial Q] (R : Subgroup Q)
    (hcomm : ⁅(⊤ : Subgroup Q), R⁆ = ⊤) : centralTrace R ≠ ⊤ := by
  intro ht
  have hR : R ≤ center Q := fun x hx =>
    show (⟨x, hx⟩ : R) ∈ centralTrace R from ht ▸ mem_top _
  have hb : ⁅(⊤ : Subgroup Q), R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hR.trans (center_le_centralizer _))
  exact top_ne_bot (hcomm.symm.trans hb)

/-- An extending automorphism preserves the actual central intersection. -/
theorem centralTrace_invariant (S R : Subgroup Q) {a : MulAut R}
    (ha : a ∈ pairAutomizer S R) {x : R} (hx : x ∈ centralTrace R) :
    a x ∈ centralTrace R := by
  obtain ⟨b, _, he⟩ := ha
  change (a x : Q) ∈ center Q
  rw [he]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := b.surjective y
  change (x : Q) ∈ center Q at hx
  simpa only [map_mul] using congrArg b (mem_center_iff.mp hx z)

/-- The central intersection supplies a common invariant line for the pair automizer. -/
theorem pairReducible_of_cyclic_centralImage [Finite Q] [Nontrivial Q]
    (S R : Subgroup Q) (hR : XiOddQuotient 3 R)
    (hcomm : ⁅(⊤ : Subgroup Q), R⁆ = ⊤) (hc : IsCyclic (centralImage R)) :
    PairReducible S R := by
  let _ := elementary_of_cyclic_centralImage R hR hc
  let _ : Fact (IsPGroup 3 R) := ⟨hR.isPGroup⟩
  let q := QuotientGroup.mk' (frattini R)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk']
    exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
  apply pairReducible_of_invariant
  refine ⟨(centralTrace R).map q, ?_, ?_, ?_⟩
  · intro hb
    exact centralTrace_ne_bot R hR hc
      (((centralTrace R).map_eq_bot_iff_of_injective hq).mp hb)
  · intro ht
    apply centralTrace_ne_top R hcomm
    apply map_injective hq
    rw [ht, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · intro a ha x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a r, centralTrace_invariant S R ha hr, (quotientAut_apply_mk _ _ _).symm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne
