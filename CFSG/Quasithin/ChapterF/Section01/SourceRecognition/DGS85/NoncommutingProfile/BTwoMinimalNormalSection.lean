module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCommutator
public import Theory.GroupAction.MinimalNormal
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.SubgroupQuotientIrreducible

/-!
# The literal minimal normal beta section

This module performs the first chief-section construction on printed p.165 of
DGS, *Groups and Graphs* (1985).  The generic engine chooses an inclusion-
minimal subgroup between a supplied denominator and numerator, retaining the
actual normalizer and quotient-conjugation hypotheses.  The reduced application
is made inside the finite beta stabilizer, so the quotient is the literal
`N / Z_beta` section of the source argument rather than a model-only copy.

The numerical lower bound and the final equality contradiction from p.165 are
subsequent source steps and remain explicit consumers of this section.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

/-- An inclusion-minimal normalized section has irreducible literal quotient
under the supplied conjugation action. -/
public theorem exists_minimal_normal_section_irreducible
    {G : Type*} [Group G] [Finite G]
    (A Q Z : Subgroup G)
    (hZQ : Z < Q)
    (hQA : Q ≤ A)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hAZ : A ≤ normalizer (Z : Set G)) :
    ∃ N : Subgroup G, ∃ hZN : Z < N, ∃ hNQ : N ≤ Q,
      ∃ hAN : A ≤ normalizer (N : Set G),
      let _ : (Z.subgroupOf N).Normal :=
        normal_subgroupOf_iff_le_normalizer hZN.le |>.mpr
          (hNQ.trans hQA |>.trans hAZ)
      ∀ f : A →* MulAut (N ⧸ Z.subgroupOf N),
        (∀ a : A, ∀ n : N,
          f a (QuotientGroup.mk' (Z.subgroupOf N) n) =
            QuotientGroup.mk' (Z.subgroupOf N)
              ⟨(a : G) * (n : G) * (a : G)⁻¹,
                (mem_normalizer_iff.mp (hAN a.property) n).mp n.property⟩) →
        ∀ K : Subgroup (N ⧸ Z.subgroupOf N),
          (∀ a n, n ∈ K → f a n ∈ K) → K = ⊥ ∨ K = ⊤ := by
  let F : Subgroup G → Prop := fun M => Z < M ∧ M ≤ Q ∧
    A ≤ normalizer (M : Set G)
  obtain ⟨N, hFN, hNQ, hNmin⟩ := exists_minimal_subgroup_of_mem_le
    (F := F) (K := Q) ⟨hZQ, le_rfl, hAQ⟩
  have hZN : Z ≤ N := hFN.1.le
  have hNQ' : N ≤ Q := hFN.2.1
  have hAN : A ≤ normalizer (N : Set G) := hFN.2.2
  have hNZ : (Z.subgroupOf N).Normal :=
    normal_subgroupOf_iff_le_normalizer hZN |>.mpr
      (hNQ'.trans hQA |>.trans hAZ)
  let _ := hNZ
  refine ⟨N, hFN.1, hNQ', hAN, ?_⟩
  dsimp only
  let _ : (Z.subgroupOf N).Normal := hNZ
  intro f hf K hK
  have hmax : ∀ M : Subgroup G, Z ≤ M → M < N →
      A ≤ normalizer (M : Set G) → M = Z := by
    intro M hZM hMNlt hAM
    by_cases hMZ : M = Z
    · exact hMZ
    · have hMN := hNmin M
        ⟨lt_of_le_of_ne hZM (Ne.symm hMZ), hMNlt.le.trans hNQ', hAM⟩ hMNlt.le
      exact False.elim ((ne_of_lt hMNlt) hMN)
  exact quotient_conjugation_irreducible_of_maximal A N Z hZN hAN hNZ hmax f hf K hK

namespace Reduction
open DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "β" => base F true

/-- The source p.165 chief-section choice in the literal finite beta
stabilizer.  The strict inclusion is retained as a source premise; the
subsequent Chapter 10 argument supplies it from the preceding core profile. -/
public theorem original_bTwo_minimal_normal_beta_section
    (h : HypothesisF11 L S)
    (hZQ : Z F β < Q F β) :
    ∃ N : Subgroup (stabilizer F β),
      ∃ _hZN : (Z F β).subgroupOf (stabilizer F β) < N,
      ∃ _hNQ : N ≤ (Q F β).subgroupOf (stabilizer F β),
      ∃ hAN : (⊤ : Subgroup (stabilizer F β)) ≤ normalizer (N : Set (stabilizer F β)),
      ∃ hNnormal : (((Z F β).subgroupOf (stabilizer F β)).subgroupOf N).Normal,
        let _ := hNnormal
        ∃ f : (⊤ : Subgroup (stabilizer F β)) →*
            MulAut (N ⧸ ((Z F β).subgroupOf (stabilizer F β)).subgroupOf N),
          (∀ a : (⊤ : Subgroup (stabilizer F β)), ∀ n : N,
            f a (QuotientGroup.mk'
              (((Z F β).subgroupOf (stabilizer F β)).subgroupOf N) n) =
              QuotientGroup.mk'
                (((Z F β).subgroupOf (stabilizer F β)).subgroupOf N)
                ⟨(a : stabilizer F β) * (n : stabilizer F β) *
                    (a : stabilizer F β)⁻¹,
                  (mem_normalizer_iff.mp (hAN a.property) n).mp n.property⟩) ∧
          ∀ K : Subgroup
              (N ⧸ ((Z F β).subgroupOf (stabilizer F β)).subgroupOf N),
            (∀ a n, n ∈ K → f a n ∈ K) → K = ⊥ ∨ K = ⊤ := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let : Finite (stabilizer F β) := (graph_locally_finite H β).1
  let Q₀ : Subgroup (stabilizer F β) := (Q F β).subgroupOf (stabilizer F β)
  let Z₀ : Subgroup (stabilizer F β) := (Z F β).subgroupOf (stabilizer F β)
  have hZ₀Q₀ : Z₀ < Q₀ := by
    have hle : Z₀ ≤ Q₀ := by
      apply (Subgroup.map_le_map_iff_of_injective
        (stabilizer F β).subtype_injective).mp
      rw [map_subgroupOf_eq_of_le (Z_le_stabilizer F β),
        map_subgroupOf_eq_of_le (Q_le_stabilizer F β)]
      exact hZQ.le
    refine ⟨hle, ?_⟩
    intro he
    apply hZQ.ne
    have hh := congrArg (fun T : Subgroup (stabilizer F β) =>
      T.map (stabilizer F β).subtype) (le_antisymm hle he)
    dsimp only [Z₀, Q₀] at hh
    simpa only [map_subgroupOf_eq_of_le (Z_le_stabilizer F β),
      map_subgroupOf_eq_of_le (Q_le_stabilizer F β)] using hh
  have hQ₀top : Q₀ ≤ (⊤ : Subgroup (stabilizer F β)) := le_top
  have hQ₀normal : Q₀.Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (Q_le_stabilizer F β)).mpr
    exact CommutingNontrivial.stabilizer_normalizes_Q F β
  let _ : Q₀.Normal := hQ₀normal
  have htopQ : (⊤ : Subgroup (stabilizer F β)) ≤ normalizer (Q₀ : Set (stabilizer F β)) :=
    le_normalizer_of_normal
  have hZ₀normal : Z₀.Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F β)).mpr
    exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F β)).mp
      (Z_normal _ β)
  let _ : Z₀.Normal := hZ₀normal
  have htopZ : (⊤ : Subgroup (stabilizer F β)) ≤ normalizer (Z₀ : Set (stabilizer F β)) :=
    le_normalizer_of_normal
  obtain ⟨N, hZN, hNQ, hAN, hf⟩ :=
    exists_minimal_normal_section_irreducible (⊤ : Subgroup (stabilizer F β)) Q₀ Z₀
      hZ₀Q₀ hQ₀top htopQ htopZ
  have hNZ : (Z₀.subgroupOf N).Normal :=
    normal_subgroupOf_iff_le_normalizer hZN.le |>.mpr
      (hNQ.trans hQ₀top |>.trans htopZ)
  refine ⟨N, hZN, hNQ, hAN, hNZ, ?_⟩
  let _ := hNZ
  obtain ⟨f, hf'⟩ := exists_quotient_conjugation_action
    (⊤ : Subgroup (stabilizer F β)) N Z₀ hAN htopZ hNZ
  refine ⟨f, hf', ?_⟩
  exact fun K hK => hf f hf' K hK

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
