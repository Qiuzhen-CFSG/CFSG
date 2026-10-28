module

public import Theory.GroupAction.CyclicAutomorphismSolvable
public import Theory.GroupAction.NormalComplement
public import Theory.GroupTheory.ZStar.SylowAutomorphismAction
public import Theory.GroupTheory.SylowPointwiseSection
public import Mathlib.GroupTheory.Nilpotent
public import FeitThompson.FinalTheorem
public import Glauberman.SylowAutomorphisms.SourceTheorem

/-!
# The unconditional two-Schreier input to layer balance

The pointwise automorphism fixer of a Sylow two-subgroup of a cyclic
simple group is solvable. Every other finite simple group has trivial
odd core by the odd order theorem. Glauberman's automorphism theorem gives
a normal odd complement in its fixer. Both that complement and the
two-group quotient are solvable, so the fixer is solvable.

The elementary fusion selection and both parts of Glauberman's theorem
are proved in the imported source assembly, using Z-star in the literal
faithful semidirect products. Applying the finite-simple conclusion to
each surjective image of a subgroup proves S₂ for every finite group,
with the actual section maps of GLS II, Definition 2.2.

Sources: GLS II, Definitions 2.2–2.3 and their remark, p.5;
Glauberman, “On the automorphism group of a finite group having no
non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Theorem 1 and Corollary 1, pp.154,157–158, DOI 10.1007/BF01111033.
The intended consumer is GLS II 5.17 and Aschbacher–Smith I.3.1.
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterI.SylowAutomorphisms

/-- The odd order theorem makes every finite group with a normal
two-complement solvable. -/
theorem solvable_of_normalTwoComplement {G : Type*} [Group G] [Finite G]
    (h : HasNormalPComplement 2 G) : Group.IsSolvable G := by
  obtain ⟨N, hn, ho, hq⟩ := h
  let : N.Normal := hn
  let : Group.IsSolvable N := odd_order_theorem N (Nat.coprime_two_left.mp ho)
  let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

/-- This includes every cyclic simple group, even when its odd core is
the whole group. -/
theorem simple_fixingSubgroup_solvable_of_solvable
    {G : Type*} [Group G] [IsSimpleGroup G] [Group.IsSolvable G]
    (S : Sylow 2 G) :
    Group.IsSolvable (fixingSubgroup (MulAut G) (S : Set G)) := by
  let : CommGroup G := { ‹Group G› with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance }
  let : IsCyclic G := inferInstance
  exact MulAut.fixingSubgroup_solvable_of_isCyclic (S : Subgroup G)

/-- The nonsolvable simple branch has trivial odd core unconditionally. -/
theorem simple_oddCore_eq_bot_of_not_solvable
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) : pPrimeCore 2 G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G) inferInstance with h | h
  · exact h
  · exfalso
    apply hns
    apply odd_order_theorem G
    have ho := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
    simpa only [h, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] using ho

/-- The reduction of the simple-group fixer to the core-free
normal-complement input. The unconditional theorem below supplies it. -/
theorem simple_fixingSubgroup_solvable_of_corefree_normalComplement
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Sylow 2 G)
    (hcomp : pPrimeCore 2 G = ⊥ →
      HasNormalPComplement 2 (fixingSubgroup (MulAut G) (S : Set G))) :
    Group.IsSolvable (fixingSubgroup (MulAut G) (S : Set G)) := by
  by_cases hs : Group.IsSolvable G
  · let : Group.IsSolvable G := hs
    exact simple_fixingSubgroup_solvable_of_solvable S
  · exact solvable_of_normalTwoComplement
      (hcomp (simple_oddCore_eq_bot_of_not_solvable hs))

/-- Every finite simple group has solvable pointwise automorphism fixers
of its Sylow two-subgroups, including the cyclic simple groups.
This supplies the simple-section input in GLS II, Definition 2.2. -/
theorem simple_fixingSubgroup_solvable
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Sylow 2 G) :
    Group.IsSolvable (fixingSubgroup (MulAut G) (S : Set G)) :=
  simple_fixingSubgroup_solvable_of_corefree_normalComplement S
    (fun hcore => Glauberman.SylowAutomorphisms.fixingSubgroup_hasNormalTwoComplement
      hcore S)

/-- GLS II, Definition 2.2: every actual simple section of a finite group
has solvable Sylow-two pointwise fixer. Surjectivity supplies finiteness
of the section; no classification or Schreier hypothesis is required. -/
theorem hasTwoSchreier (G : Type*) [Group G] [Finite G] :
    Theory.GroupTheory.HasTwoSchreier G := by
  intro U S _ _ f hf P
  let : Finite S := Finite.of_surjective f hf
  exact simple_fixingSubgroup_solvable P

end CFSG.Quasithin.ChapterI.SylowAutomorphisms
