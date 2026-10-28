module

public import Theory.GroupTheory.RankTwoDisjointAction
public import CFSG.Quasithin.Defs

/-!
# Elementary planes in strongly quasithin groups

An odd elementary plane cannot normalize a disjoint subgroup with order
divisible by its prime: fixed-point counting would produce an elementary
subgroup of rank three. Faithfulness on a normalized subgroup makes its
centralizer disjoint from the plane, giving the second conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.27, printed p.26. The centralizer theorem below applies to every
faithfully acted-on subgroup, including the elementary two-subgroups of
the printed statement.
-/

namespace CFSG.Quasithin.ChapterA
open Subgroup

/-- A.1.27(1): a subgroup normalized disjointly by an odd elementary plane
has order prime to p in an SQT-group. -/
public theorem lemma_A_1_27_1
    {G : Type*} [Group G] [Finite G] (hG : IsStronglyQuasithin G)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P H : Subgroup G)
    [IsElementaryAbelian p P] (hc : Nat.card P = p ^ 2)
    (hn : P ≤ normalizer (H : Set G)) (hd : Disjoint P H) :
    Nat.Coprime p (Nat.card H) :=
  coprime_card_of_normalized_disjoint_plane (hG p Fact.out hp) P H hc hn hd

/-- A.1.27(2), in the stronger form allowing any normalized subgroup U:
the actual conjugation action of the plane is faithful, so C_G(U) is a
p'-group. No assumption on U beyond normalization and faithfulness is needed. -/
public theorem lemma_A_1_27_2
    {G : Type*} [Group G] [Finite G] (hG : IsStronglyQuasithin G)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P U : Subgroup G)
    [IsElementaryAbelian p P] (hc : Nat.card P = p ^ 2)
    (hn : P ≤ normalizer (U : Set G))
    (hfaith : Function.Injective (U.normalizerMonoidHom.comp (inclusion hn))) :
    Nat.Coprime p (Nat.card (centralizer (U : Set G))) :=
  coprime_card_centralizer_of_faithful_plane (hG p Fact.out hp) P U hc hn hfaith

end CFSG.Quasithin.ChapterA
