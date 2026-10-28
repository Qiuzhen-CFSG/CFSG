module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CaseII

/-!
# Local inputs to Janko's character calculation

This interface separates the local group analysis from the character
argument. Its fields are selected conclusions of Janko's Sections 2–5
and Lemma 13, not hypotheses of the recognition theorem. Their existence
from a Case II centralizer still has to be proved. The order calculation
may use this interface conditionally while that proof is developed.

All subgroups are actual subgroups of the ambient group. In particular,
the complements to E and F lie in their respective normalizers, and their
group types are expressed by multiplicative equivalences. Conjugacy and
centralizers in the counting clauses are ambient. The normalizer
alternative retains order 144 until the ambient order has been proved.
Neither the ambient order nor an ambient model identification is a field.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, pp.4–10 and 14,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

namespace CaseII

/-- Representatives for the identity, involutions, and the classes of
orders 3, 4, 4, 6, 8 appearing in the centralizer and Sylow subgroup. -/
@[expose] public def classRepresentative : Fin 7 → TwistedModel :=
  ![1, z 0, c, z 3 * a, z 1 * d, c * z 0, z 1 * b * d]

end CaseII

/-- The local conclusions needed by the subsequent character argument.
Constructing this record is a separate group-theoretic proof obligation. -/
public structure LocalAnalysisData {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  /-- The first source subgroup is elementary of order sixteen. -/
  E_elementary : IsElementaryAbelian 2 (CaseII.E D k)
  E_card : Nat.card (CaseII.E D k) = 16
  /-- Its centralizer in the ambient group is itself. -/
  E_centralizer : centralizer (CaseII.E D k : Set G) = CaseII.E D k
  /-- The second source subgroup is elementary of order sixteen. -/
  F_elementary : IsElementaryAbelian 2 (CaseII.F D k)
  F_card : Nat.card (CaseII.F D k) = 16
  F_centralizer : centralizer (CaseII.F D k : Set G) = CaseII.F D k
  /-- Lemma 6: the first normalizer splits over its actual E16, with A6 complement. -/
  normalizer_E : ∃ K : Subgroup (normalizer (CaseII.E D k : Set G)),
    ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K ∧
      Nonempty (K ≃* alternatingGroup (Fin 6))
  /-- Lemmas 2 and 7: the second normalizer splits over its actual E16, with S5 complement. -/
  normalizer_F : ∃ K : Subgroup (normalizer (CaseII.F D k : Set G)),
    ((CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G))).IsComplement' K ∧
      Nonempty (K ≃* Equiv.Perm (Fin 5))
  /-- Lemma 7: all involutions are fused in the ambient group. -/
  involution_fusion : ∀ x : G, orderOf x = 2 → IsConj x D.z
  /-- Lemma 8: all elements of order three are fused in the ambient group. -/
  three_fusion : ∀ x : G, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c)
  /-- Lemma 8: the actual Sylow three-groups are elementary and self-centralizing. -/
  sylow_three : ∀ P : Sylow 3 G,
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ centralizer (P : Set G) = P
  /-- Only the orders of the three structural alternatives in Lemma 8
  are needed for the order calculation. -/
  normalizer_three : ∀ P : Sylow 3 G,
    Nat.card (normalizer (P : Set G)) = 72 ∨ Nat.card (normalizer (P : Set G)) = 144
  /-- The consequence of Lemma 9 used in the order argument. -/
  nonabelian_twenty_one : ∃ A : Subgroup G, Nat.card A = 21 ∧
    ∃ x y : A, x * y ≠ y * x
  /-- Lemma 10: the two distinct ambient classes of elements of order four. -/
  four_fusion : ∀ x : G, orderOf x = 4 →
    IsConj x (CaseII.into D k (CaseII.z 3 * CaseII.a)) ∨
      IsConj x (CaseII.into D k (CaseII.z 1 * CaseII.d))
  four_not_fused : ¬ IsConj (CaseII.into D k (CaseII.z 3 * CaseII.a))
    (CaseII.into D k (CaseII.z 1 * CaseII.d))
  /-- The ambient centralizer orders in Lemma 10. -/
  centralizer_orders : ∀ i : Fin 4,
    Nat.card (centralizer ({CaseII.into D k
      (![CaseII.z 3 * CaseII.a, CaseII.z 1 * CaseII.d,
          CaseII.z 1 * CaseII.b * CaseII.d, CaseII.c * CaseII.z 0] i)} : Set G)) =
      ![32, 16, 8, 12] i
  /-- Lemma 10's distribution, counted using ambient conjugacy. -/
  centralizer_distribution : ∀ i : Fin 7,
    Nat.card {x : D.centralizer //
      IsConj (x : G) (CaseII.into D k (CaseII.classRepresentative i))} =
      ![1, 51, 32, 84, 72, 96, 48] i
  /-- Lemma 13's distribution for the original ambient Sylow two-group. -/
  sylow_distribution : ∀ i : Fin 7,
    Nat.card {x : D.sylow //
      IsConj (x : G) (CaseII.into D k (CaseII.classRepresentative i))} =
      ![1, 35, 0, 36, 40, 0, 16] i

end Theory.GroupTheory.HeldM22A10.M22Identification
