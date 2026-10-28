module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# Intermediate conclusions for the Case II analysis

These are separate outputs of Janko's involution, three-local and class
counting arguments. None has an assumed inhabitant. A conditional proof of
the later arguments may use the earlier conclusions, but the construction
of `LocalAnalysisData` must supply all three from the original `LocalData`
and the Case II equivalence.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Sections 2–5 and Lemma 13.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- The conclusions of Section 2 still requiring the ambient group argument. -/
public structure InvolutionNormalizerData {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  normalizer_E : ∃ K : Subgroup (normalizer (CaseII.E D k : Set G)),
    ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K ∧
      Nonempty (K ≃* alternatingGroup (Fin 6))
  normalizer_F : ∃ K : Subgroup (normalizer (CaseII.F D k : Set G)),
    ((CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G))).IsComplement' K ∧
      Nonempty (K ≃* Equiv.Perm (Fin 5))
  involution_fusion : ∀ x : G, orderOf x = 2 → IsConj x D.z

/-- The selected conclusions of Sections 3–4; these do not assert the
ambient order or omit the possible order-144 three-normalizer. -/
public structure ThreeLocalData {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  three_fusion : ∀ x : G, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c)
  sylow_three : ∀ P : Sylow 3 G,
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ centralizer (P : Set G) = P
  normalizer_three : ∀ P : Sylow 3 G,
    Nat.card (normalizer (P : Set G)) = 72 ∨ Nat.card (normalizer (P : Set G)) = 144
  nonabelian_twenty_one : ∃ A : Subgroup G, Nat.card A = 21 ∧
    ∃ x y : A, x * y ≠ y * x

/-- The remaining class counts, with ambient conjugacy and the original
Sylow subgroup, as in Lemmas 10 and 13. -/
public structure LocalClassDistributions {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : Prop where
  centralizer_distribution : ∀ i : Fin 7,
    Nat.card {x : D.centralizer //
      IsConj (x : G) (CaseII.into D k (CaseII.classRepresentative i))} =
      ![1, 51, 32, 84, 72, 96, 48] i
  sylow_distribution : ∀ i : Fin 7,
    Nat.card {x : D.sylow //
      IsConj (x : G) (CaseII.into D k (CaseII.classRepresentative i))} =
      ![1, 35, 0, 36, 40, 0, 16] i

end Theory.GroupTheory.HeldM22A10.M22Identification
