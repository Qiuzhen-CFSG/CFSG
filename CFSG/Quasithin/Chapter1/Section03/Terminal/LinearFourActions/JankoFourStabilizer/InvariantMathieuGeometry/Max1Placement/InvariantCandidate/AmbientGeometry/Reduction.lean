module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.CoreRecovery

/-!
# Transport of ambient core bounds from the literal max1 embedding

An abstract isomorphism with max1 transports intrinsic group theory but does
not compare ambient centralizers. An actual conjugation in J₄ does: it carries
the section, its ambient Sylow subgroup, the candidate, and both embedded
two-cores to their images. Pulling back the literal centralizer and normalizer
bounds then gives `AmbientCoreRecovery`.

The three contracts below are separate unproved geometric obligations. The
conjugacy contract retains both source-local hypotheses; it does not assert
that the original Sylow lies in the candidate. The centralizer contract fixes
the candidate to the literal max1 embedding while retaining those hypotheses.
The normalizer contract is a single ambient calculation for that embedding.
None assumes intrinsic core recovery, simplicity, or perfectness of J₄.

Source: Aschbacher–Smith A.3.12(17) and its Sylow-overgroup proof, printed
pp.47–48, and the proof of 1.3.9, p.514. GLS3 Table 5.3i identifies
N(O₂(C(2B))) with E₂¹¹.M₂₄. The table and the checked intrinsic max1 structure
do not establish any of these three contracts for the matrix model.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels

namespace AmbientGeometry

/-- An actual ambient conjugation places a source-local candidate in the
literal certified max1 subgroup. This is stronger than its supplied abstract
isomorphism, and remains a geometric proof obligation. -/
@[expose] def CandidateConjugacy : Prop :=
  ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (H : Subgroup Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
    A ∈ ChapterA.Section03.localCComponents S → H ∈ candidates A →
    ∃ g : Janko4.Model,
      H.map (MulAut.conj g).toMonoidHom = certifiedMathieuSubgroup

/-- The ambient centralizer calculation for source-local sections whose
candidate is the literal max1 subgroup. The two Sylow witnesses remain
independent; neither ambient Sylow containment nor normality in max1 is assumed. -/
@[expose] def LiteralCentralizerControl : Prop :=
  ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
    A ∈ ChapterA.Section03.localCComponents S →
    certifiedMathieuSubgroup ∈ candidates A →
    centralizer (coreCenter A : Set Janko4.Model) ≤ certifiedMathieuSubgroup

/-- The normalizer in J₄ of the embedded two-core of literal max1 stays in
max1. Intrinsic normality supplies the reverse inclusion, not this bound. -/
@[expose] def LiteralCoreNormalizerControl : Prop :=
  normalizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Janko4.Model) ≤
    certifiedMathieuSubgroup

private theorem centralizer_coreCenter_le_of_map
    {G G' : Type*} [Group G] [Group G'] (A H : Subgroup G) (e : G ≃* G')
    (h : centralizer (coreCenter (A.map e.toMonoidHom) : Set G') ≤
      H.map e.toMonoidHom) :
    centralizer (coreCenter A : Set G) ≤ H := by
  intro x hx
  have he : e x ∈ centralizer (coreCenter (A.map e.toMonoidHom) : Set G') := by
    rw [← map_coreCenter A e]
    rintro y ⟨z, hz, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e.toMonoidHom (hx z hz)
  obtain ⟨y, hy, hyx⟩ := h he
  exact e.injective hyx ▸ hy

private theorem normalizer_core_le_of_map
    {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (e : G ≃* G')
    (h : normalizer ((H.map e.toMonoidHom).pCoreIn 2 : Set G') ≤
      H.map e.toMonoidHom) :
    normalizer (H.pCoreIn 2 : Set G) ≤ H := by
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [map_equiv_normalizer_eq,
    map_pCoreIn_of_injective 2 H e.toMonoidHom e.injective]
  exact h

private theorem local_map_equiv
    {A S : Subgroup Janko4.Model}
    (hA : A ∈ ChapterA.Section03.localCComponents S) (e : MulAut Janko4.Model) :
    A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact Section02.localCComponents_map_of_solvable_ker hA e.toMonoidHom

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- Conditional assembly of the two ambient bounds. All three geometric
premises still need proofs before this yields `ambientCoreRecovery`. -/
theorem ambientCoreRecovery_of_literal_geometry
    (hconj : CandidateConjugacy) (hcent : LiteralCentralizerControl)
    (hnorm : LiteralCoreNormalizerControl) : AmbientCoreRecovery := by
  intro A S H hA hlocal hH
  obtain ⟨g, hg⟩ := hconj A S H hA hlocal hH
  let e := MulAut.conj g
  change H.map e.toMonoidHom = certifiedMathieuSubgroup at hg
  let B := A.map e.toMonoidHom
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2 := by
    let f : A ≃* B := e.subgroupMap A
    exact hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  have hT : B ∈ ChapterA.Section03.localCComponents T :=
    local_map_equiv hlocal e
  have hM : certifiedMathieuSubgroup ∈ candidates B := by
    rw [← hg]
    exact map_mem_candidates hH e
  constructor
  · apply centralizer_coreCenter_le_of_map A H e
    rw [hg]
    exact hcent B T hB hT hM
  · apply normalizer_core_le_of_map H e
    rw [hg]
    exact hnorm

end AmbientGeometry
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
