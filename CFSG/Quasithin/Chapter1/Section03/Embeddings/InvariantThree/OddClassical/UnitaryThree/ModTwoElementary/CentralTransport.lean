module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Transport

/-!
# Transport of the elementary odd-unitary pair through every central cover

An order-nine complement in `PairInput` is elementary abelian. If the pair
is nonreducible, its intersection with the ambient center lies in its trivial
Frattini subgroup. Projection followed by an actual model isomorphism is
therefore an isomorphism on the complement. It preserves the Sylow subgroup,
permutability, and all extending pair automorphisms. Pullback along the induced
Frattini equivalence transports each two-group's proper nonzero invariant subgroup.

This completes the central-cover step without a multiplier assumption. The
matrix-model action calculation remains a separate input to the last theorem.
The generic action transport reuses the linear and sporadic transport modules;
no family-specific exclusion from those modules is invoked.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
open EvenRankTwo.Linear.Actions
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
namespace UnitaryThree.ModTwoElementary

omit [Finite Q] in
/-- The order-nine branch of the supplied odd-complement alternative is elementary. -/
theorem elementary_of_card_nine {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hcard : Nat.card R = 9) : IsElementaryAbelian 3 R := by
  rcases h.oddComplement with ⟨he, _⟩ | ⟨_, hc, _⟩
  · exact he
  · norm_num at hc
    omega

/-- An elementary nonreducible complement embeds in the central quotient. -/
theorem disjoint_center_of_nonreducible {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hcard : Nat.card R = 9)
    (hn : ¬ PairReducible (S : Subgroup Q) R) : Disjoint R (center Q) := by
  let _ := elementary_of_card_nine h hcard
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  apply Disjoint.symm
  apply subgroupOf_eq_bot.mp
  apply bot_unique
  simpa only [frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3)] using
    center_intersection_le_frattini h hn

variable {G : Type v} [Group G]

/-- Pull back each invariant subgroup through the genuine Frattini equivalence. -/
theorem reducible_of_central_image {S : Sylow 2 Q} {R : Subgroup Q}
    (e : Q ⧸ center Q ≃* G) (hd : Disjoint R (center Q))
    (hr : PairReducible (centralImageSylow e S : Subgroup G)
      (R.map (centralModelMap e))) : PairReducible (S : Subgroup Q) R := by
  intro D hD htwo
  let a := MulAut.congr (centralImageEquiv e R hd)
  let D' := D.map a.toMonoidHom
  obtain ⟨hD', htwo'⟩ := centralImage_twoGroup e S R hd D hD htwo
  obtain ⟨A, hAb, hAt, hA⟩ := hr D' hD' htwo'
  let f := SporadicActions.frattiniEquiv (centralImageEquiv e R hd)
  refine ⟨A.comap f.toMonoidHom, ?_, ?_, ?_⟩
  · intro hb
    apply hAb
    have hh := congrArg (Subgroup.map f.toMonoidHom) hb
    rw [map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective A,
      Subgroup.map_bot] at hh
    exact hh
  · intro ht
    apply hAt
    have hh := congrArg (Subgroup.map f.toMonoidHom) ht
    rw [map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective A,
      map_top_of_surjective f.toMonoidHom f.surjective] at hh
    exact hh
  · intro b hb x hx
    change f (quotientAut (frattini R) b x) ∈ A
    rw [SporadicActions.frattiniEquiv_equivariant]
    exact hA (a b) ⟨b, hb, rfl⟩ (f x) hx

/-- A local elementary-pair calculation in the central quotient handles every
central cover. All subgroup, cardinality and action transport is discharged here. -/
theorem reducible_of_elementary_model {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hcard : Nat.card R = 9) (e : Q ⧸ center Q ≃* G)
    (hmodel : ∀ (T : Sylow 2 G) (U : Subgroup G), IsElementaryAbelian 3 U →
      Nat.card U = 9 → (U : Set G) * (T : Set G) = (T : Set G) * (U : Set G) →
      PairReducible (T : Subgroup G) U) : PairReducible (S : Subgroup Q) R := by
  by_contra hn
  have hd := disjoint_center_of_nonreducible h hcard hn
  let f := centralModelMap e
  let U := R.map f
  let T := centralImageSylow e S
  have hU : Nat.card U = 9 := (Nat.card_congr (centralImageEquiv e R hd).toEquiv).symm.trans hcard
  let _ := elementary_of_card_nine h hcard
  have he : IsElementaryAbelian 3 U := IsElementaryAbelian.map f
  have hp : (U : Set G) * (T : Set G) = (T : Set G) * (U : Set G) := by
    have hh := congrArg (Set.image f) h.permutes
    change (R.map f : Set G) * ((S : Subgroup Q).map f : Set G) =
      ((S : Subgroup Q).map f : Set G) * (R.map f : Set G)
    simpa only [Set.image_mul, Subgroup.coe_map, Sylow.coe_coe] using hh
  exact hn (reducible_of_central_image e hd (hmodel T U he hU hp))

end UnitaryThree.ModTwoElementary
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
