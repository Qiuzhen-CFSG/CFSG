module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureSylowGeneration
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# Corrected model selection for a section of the neighboring center

The original actor A lies in Q_delta and escapes Q_lambda. Its actual image
in X/(X intersect Q_lambda) is nontrivial and lies in the Sylow obtained by
intersecting X with the full Borel core. A literal double commutator bound
makes this actor quadratic on the specified section of Z_lambda. The
original centralizer-index upper bound then gives the strict comparison
required by corrected 5.12. Sylow fixed generation is proved from the
original seed, rather than assumed, and the output retains the actual
field, group isomorphism, section vectors and natural coordinates.

This is a conditional noncentral module selection step toward DGS 6.4,
pp.120--121, using corrected 5.12, pp.113--115. The source assembly must
still construct the faithful section, its residual fixed-space vanishing,
the full catalogue marking and the replacement actor with its index bound.
In particular a center centralized by X cannot supply that faithful module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Corrected 5.12 on the original closure section: generation, Sylow placement
and strictness follow from the original subgroup and index premises. -/
theorem source_closure_section_model_selection
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (C A : Subgroup G)
    (σ : Representation (ZMod 2) D W)
    (π : conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) →* D)
    (hπ : Function.Surjective π)
    (hk : π.ker = ((P (other i)).pCoreIn 2).subgroupOf
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))))
    (d : BinaryConjugationSection (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))
      (sylowCenterSpan (P (other i))) C (σ.comp π))
    (M : BinaryRankOneModel D) (hf : Function.Injective σ)
    (hres : fixedSpace σ (pResidual 2 D) = ⊥)
    (hA : A ≤ (P i).pCoreIn 2) (hout : ¬ A ≤ (P (other i)).pCoreIn 2)
    (hquad : ⁅A,⁅A,sylowCenterSpan (P (other i))⁆⁆ ≤ C)
    (hindex : (centralizer (A : Set G)).relIndex (sylowCenterSpan (P (other i))) ≤
      ((P (other i)).pCoreIn 2).relIndex A) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = B.pCoreIn 2 ⊓ X ∧
      ∃ U : Sylow 2 D, (U : Subgroup D) = (T : Subgroup X).map π ∧
        NaturalRealization σ U := by
  let R := P (other i)
  let := (Classical.choice (h.local_data (other i))).finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) R
  have hBP : B ≤ R := le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hXP : X ≤ R := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans hBP)
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  let : Finite D := Finite.of_surjective π hπ
  let Z := sylowCenterSpan R
  let : Finite Z := Finite.of_injective (inclusion (sylowCenterSpan_le R)) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun z : Z => (d.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  obtain ⟨T,hT⟩ := source_closure_sylow_intersection h hB hS i
  have hAX : A ≤ X := hA.trans (le_conjugateSpanBy _ _)
  have hAS : A ≤ B.pCoreIn 2 := hA.trans (pGroup_le_core_of_core_sylow B _
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB)
  have hAT : A.subgroupOf X ≤ (T : Subgroup X) := by
    intro a ha
    have hh : (a : G) ∈ (T : Subgroup X).map X.subtype := hT.symm ▸ ⟨hAS ha,a.property⟩
    obtain ⟨t,ht,he⟩ := hh
    exact (X.subtype_injective he) ▸ ht
  let I := (A.subgroupOf X).map π
  have hIc : Nat.card I = ((P (other i)).pCoreIn 2).relIndex A :=
    actor_image_card_eq_relIndex X _ A π hk hAX
  have hIn : 1 < Nat.card I := by
    have hi : 1 < ((P (other i)).pCoreIn 2).relIndex A := by
      have hne : ((P (other i)).pCoreIn 2).relIndex A ≠ 1 := by
        intro he
        exact hout ((relIndex_eq_one).mp he)
      let : Finite A := Finite.of_injective (inclusion hAX) (inclusion_injective _)
      have hp : 0 < ((P (other i)).pCoreIn 2).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
      omega
    rwa [hIc]
  have hg := source_closure_section_generated h hB hS i hn C σ π d T (hT.le.trans inf_le_left)
  have hq := isQuadratic_of_triple_commutator_le X Z C A σ π d hquad
  have hb := fixed_quotient_card_le_centralizer_index σ π d A
  have hs : Nat.card (W ⧸ fixedSpace σ I) < Nat.card I ^ 2 := by
    have hi : Nat.card (W ⧸ fixedSpace σ I) ≤ Nat.card I := by
      exact (hb.trans hindex).trans_eq hIc.symm
    exact hi.trans_lt (by nlinarith)
  exact ⟨T,hT,T.mapSurjective hπ,rfl,(binary_rank_one_bound_and_recognition M σ hf (T.mapSurjective hπ) I
    (map_mono hAT) hq hg hres).2 hs⟩

end CFSG.Quasithin.ChapterF.Source.DGS85
