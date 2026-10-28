module
public import CFSG.Quasithin.Chapter14.Section02.LargeModels
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original exchanged Bender subgroup for 14.2.8

In the paired branch the original maximal core equals O₂(H). Transport the
actual marked component image across that equality and the C-component
quotient equivalence. This gives K₁/O₂(K₁) as binary PSL₂ or Suzuki on the
original carrier. The same K₁ remains a C-component in K₁N_T(K₁), and its
normalizer in T has index two. The odd paired row is excluded by its proved
rank-one generation bound. Source: Aschbacher--Smith E.2.2(1) and 14.2.8(2),
printed pp.215--216 and 983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

private noncomputable def quotientImageEquivOfEq (N D : Subgroup H) [N.Normal] [D.Normal]
    (he : N = D) (K : Subgroup H) :
    K.map (QuotientGroup.mk' N) ≃* K.map (QuotientGroup.mk' D) := by
  subst D
  exact MulEquiv.refl _

theorem paired_original_bender_quotient
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) {f : ℕ}
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H))
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) K f) :
    (2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
      ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have e : (K ⧸ pCore 2 K) ≃* sourceImage (ChapterB.minimalParabolicMax T hP) K := by
    exact (cComponentTwoCoreQuotientEquiv hK).trans
      (quotientImageEquivOfEq _ _ hc.kernel_eq K).symm
  rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,d,hB⟩ | ⟨m,hm,hf,d,hB⟩
  · exact Or.inl ⟨hf,F,hF,hfin,hcard,⟨e.trans d⟩⟩
  · exact Or.inr ⟨m,hm,hf,⟨e.trans d⟩⟩

/-- The source's exchanged K₁ has its original two-core quotient and local carrier. -/
theorem source_paired_large_bender
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal) :
    let S := (T : Subgroup H) ⊓ normalizer (K : Set H)
    ChapterB.minimalParabolicCore T hP = pCore 2 H ∧
      S.relIndex (T : Subgroup H) = 2 ∧
      (K.subgroupOf (K ⊔ S)).IsCComponent ∧
      ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
        ExchangedModel (ChapterB.minimalParabolicMax T hP) K f ∧
        ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
          ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
            Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    hH T hP hs hK hqK hgen hnot
  have hi : (normalizer (K : Set H)).index = 2 :=
    (Structure.source_original_component_normal_or_index_two ChapterA.Section02.theoremA_knownSimple
      hH T hP hs K hK hgen).resolve_left hnot
  have hTN : ¬(T : Subgroup H) ≤ normalizer (K : Set H) := by
    intro ht
    have hh : (⊤ : Subgroup H) ≤ normalizer (K : Set H) := hgen ▸ sup_le K.le_normalizer ht
    exact hnot (normalizer_eq_top_iff.mp (top_unique hh))
  refine ⟨hc.kernel_eq,?_,hK.subgroupOf le_sup_left,?_⟩
  · rw [inf_relIndex_left]
    exact subgroupOf_index_eq_two _ _ hi hTN
  · rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen hnot with
      ⟨f,hf,hm⟩ | ⟨p,hp,ho,hp7,hm⟩
    · exact ⟨f,(Inverted.source_exchanged_intrinsic_escape hH T hP hs K hK hqK hgen hnot hm).2.1,
        hf,hm,paired_original_bender_quotient T hP K hK hc hm⟩
    · let : Fact p.Prime := ⟨hp⟩
      exact ((Nat.not_le_of_gt hn) (Structure.NumericalBounds.paired_prime_upper_one
        ChapterA.Section02.theoremA_knownSimple hH T hP hs K hK hgen hnot hp7 hm)).elim
end CFSG.Quasithin.Chapter14.Section02
