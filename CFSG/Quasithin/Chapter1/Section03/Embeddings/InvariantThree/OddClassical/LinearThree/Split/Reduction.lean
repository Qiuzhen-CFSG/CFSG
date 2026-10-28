module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Basic

/-!
# Invariant intersections for the split odd PSL₃ branch

For an elementary order-nine complement, an order-three intersection with
Z(Q) or with the derived subgroup of C_Q(Z(S)) gives a common invariant line.
The second subgroup is preserved by every automorphism of Q preserving S;
thus the argument applies to the full pair automizer, including outer actions.
All subgroup invariance and Frattini-quotient steps are proved here.

The central intersection matters for actual SL₃ covers. It cannot in general
be replaced by an intersection with the derived centralizer. The two
intersection cardinalities, and the order-nine local-core calculation for an
extraspecial complement, still require separate matrix-group proofs.

`SplitPrimeCover` states the universal earlier cover input with actual model
equivalences. The ordinary scalar kernel does not establish that input.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528); I.1.3, printed p.407 (PDF p.418).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
universe u
variable {Q : Type u} [Group Q]

/-- The universal cover consequence of I.1.3 for split odd primes. This is an
explicit earlier-result input, independent of the pair and its action. The
conclusion retains actual SL₃ and PSL₃ equivalences via `LinearThreeModel`. -/
def SplitPrimeCover : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → 3 < p → p % 3 = 1 →
    ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
      ClassicalGroup.IsPSL (K ⧸ center K) 3 p → LinearThreeModel p K

/-- The commutator subgroup of the centralizer of the intrinsic center of S. -/
def centralizerDerived (S : Subgroup Q) : Subgroup Q :=
  let Z : Subgroup Q := S ⊓ centralizer (S : Set Q)
  let C := centralizer (Z : Set Q)
  ⁅C, C⁆

/-- The ambient definition is exactly the derived subgroup of C_Q(Z(S)). -/
theorem centralizerDerived_eq_center (S : Subgroup Q) :
    centralizerDerived S =
      let C := centralizer ((center S).map S.subtype : Set Q)
      ⁅C, C⁆ := by
  have hZ : (center S).map S.subtype = S ⊓ centralizer (S : Set Q) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, fun y hy => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, mem_center_iff.mpr (fun y => ?_), rfl⟩
      exact Subtype.ext (hc y y.property)
  rw [hZ]
  rfl

private theorem map_centralizer (E : Subgroup Q) (a : MulAut Q) :
    (centralizer (E : Set Q)).map a.toMonoidHom =
      centralizer (E.map a.toMonoidHom : Set Q) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    intro y hy
    apply a.injective
    simpa only [map_mul, a.apply_symm_apply] using hx (a y) (mem_map_of_mem _ hy)

/-- Every ambient automorphism preserving S preserves the chosen subgroup. -/
theorem centralizerDerived_map (S : Subgroup Q) (a : MulAut Q)
    (hS : S.map a.toMonoidHom = S) :
    (centralizerDerived S).map a.toMonoidHom = centralizerDerived S := by
  have hZ : (S ⊓ centralizer (S : Set Q)).map a.toMonoidHom =
      S ⊓ centralizer (S : Set Q) := by
    rw [map_inf _ _ a.toMonoidHom a.injective, map_centralizer S a, hS]
  have hC := map_centralizer (S ⊓ centralizer (S : Set Q)) a
  rw [hZ] at hC
  unfold centralizerDerived
  rw [map_commutator, hC]

/-- An order-three intersection with the canonical derived subgroup is an
invariant line in the elementary complement. -/
theorem reducible_of_elementary_centralizerDerived_three [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    (hA : Nat.card ((centralizerDerived (S : Subgroup Q)).subgroupOf R) = 3) :
    PairReducible (S : Subgroup Q) R := by
  let _ := he
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  apply reducible_of_invariant_subgroup (S : Subgroup Q) R
    ((centralizerDerived (S : Subgroup Q)).subgroupOf R)
  · rw [frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3)]
    intro ha
    have hh := bot_unique ha
    rw [hh, Subgroup.card_bot] at hA
    omega
  · intro ha
    rw [ha, Nat.card_congr Subgroup.topEquiv.toEquiv, hc] at hA
    omega
  · intro b hb x hx
    obtain ⟨a, hS, he⟩ := hb
    have hS' : (S : Subgroup Q).map a.toMonoidHom = S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hS z).mpr hz
      · intro hy
        exact ⟨a.symm y, (hS _).mp (by simpa using hy), a.apply_symm_apply y⟩
    change (b x : Q) ∈ centralizerDerived (S : Subgroup Q)
    rw [he]
    have hx' : (x : Q) ∈ centralizerDerived (S : Subgroup Q) := hx
    have hh := mem_map_of_mem a.toMonoidHom hx'
    rw [centralizerDerived_map _ a hS'] at hh
    exact hh

/-- A central order-three intersection is an invariant line, including in
a nontrivial central cover. -/
theorem reducible_of_elementary_center_three [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    (hA : Nat.card ((center Q).subgroupOf R) = 3) :
    PairReducible (S : Subgroup Q) R := by
  let _ := he
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  apply reducible_of_characteristic_intersection (S : Subgroup Q) R (center Q)
  · rw [frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3)]
    intro ha
    have hh := bot_unique ha
    rw [hh, Subgroup.card_bot] at hA
    omega
  · intro ha
    rw [ha, Nat.card_congr Subgroup.topEquiv.toEquiv, hc] at hA
    omega

/-- Either concrete intersection calculation excludes the elementary pair. -/
theorem reducible_of_elementary_intersections [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    (hA : Nat.card ((center Q).subgroupOf R) = 3 ∨
      Nat.card ((centralizerDerived (S : Subgroup Q)).subgroupOf R) = 3) :
    PairReducible (S : Subgroup Q) R := by
  rcases hA with hz | hd
  · exact reducible_of_elementary_center_three h he hc hz
  · exact reducible_of_elementary_centralizerDerived_three h he hc hd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
