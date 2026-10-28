module
public import CFSG.Quasithin.Chapter14.Section02.PairedKOne
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.PerfectCentralCoverOddRankRigidity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.Suzuki.OddSubgroups
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original normal linear and Suzuki subgroup in 14.2.8

The map from K/O₂(K) to the marked simple image in H/J is a perfect
central cover. Its two-core is trivial and every odd Sylow subgroup of
the marked PSL₂ or Suzuki group is cyclic, so transfer kills its kernel.
The source center identity then gives J = O₂(H). A normal generating
C-component is the actual two-residual, and its Sylow normalizer is the
whole prescribed Sylow subgroup. These statements use the original
component and quotient maps, before any rank-two amalgam is selected.

Source: Aschbacher--Smith E.2.2(2a) and 14.2.8(1), printed pp.215--216
and 983. The separate unitary Bender row is not excluded here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- The actual component map after removing its two-core is a perfect central cover. -/
noncomputable def originalComponentStarCover
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K)
      (sourceImage (ChapterB.minimalParabolicMax T hP) K) := by
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  have hk : pCore 2 K ≤ (q.subgroupMap K).ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : H)).mpr
      (ChapterB.minimalParabolicTwoCore_le_core T hP
        (pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hx)))
  let f := QuotientGroup.lift (pCore 2 K) (q.subgroupMap K) hk
  let := hqK
  let : IsQuasisimple (sourceImage (ChapterB.minimalParabolicMax T hP) K) :=
    (source_component_simple_image T hP hs K hK hgen).2.1.2
  let : IsQuasisimple (K.map q) :=
    (source_component_simple_image T hP hs K hK hgen).2.1.2
  let c : Covering (K ⧸ pCore 2 K) (K.map q) :=
    ⟨f,QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective K) _⟩
  exact PerfectCentralCovering.ofCovering c

private theorem marked_rank_one_odd_ranks
    (M K : Subgroup H) {f : ℕ} (hm : ExchangedModel M K f) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p (sourceImage M K) ≤ 1 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with ⟨F,hF,hfin,hchar,_,_,d,_⟩ | ⟨m,hm,_,d,_⟩
  · rw [primeRank_equiv p (d.trans (Theory.PSL2.sl2QuotientEquiv F).symm)]
    exact Matrix.SL2.binary_odd_primeRank_le_one ho
  · rw [primeRank_equiv p d]
    let P : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := default
    exact P.primeRank_le_one_of_isCyclic
      (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega)
        (fun he => ho.not_two_dvd_nat (by rw [he])) P)

/-- The original component quotient is its marked linear or Suzuki simple image. -/
theorem original_rank_one_quotient_equiv
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) K f) :
    Nonempty ((K ⧸ pCore 2 K) ≃*
      sourceImage (ChapterB.minimalParabolicMax T hP) K) := by
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  have ho : Odd (Nat.card c.toMonoidHom.ker) := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) _ c.ker_le_center)
  have hk := c.ker_eq_bot_of_odd_of_odd_primeRank_le_one ho
    (marked_rank_one_odd_ranks _ _ hm)
  exact ⟨MulEquiv.ofBijective c.toMonoidHom
    ⟨c.toMonoidHom.ker_eq_bot_iff.mp hk,c.surjective⟩⟩

/-- All original K₁ assertions in the normal PSL₂/Suzuki branch of 14.2.8. -/
theorem source_normal_rank_one_kOne
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) K f) :
    pResidual 2 H = K ∧
      ChapterB.minimalParabolicCore T hP = pCore 2 H ∧
      (T : Subgroup H) ⊓ normalizer (K : Set H) = (T : Subgroup H) ∧
      (K.subgroupOf (K ⊔ (T : Subgroup H))).IsCComponent ∧
      ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
        ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  obtain ⟨e⟩ := original_rank_one_quotient_equiv T hP hs K hK hqK hgen hm
  have hc := source_original_normal_clauses T hP hs K hK hqK hgen
  let := hqK
  let : IsSimpleGroup (sourceImage (ChapterB.minimalParabolicMax T hP) K) :=
    (source_component_simple_image T hP hs K hK hgen).1
  let : IsQuasisimple (sourceImage (ChapterB.minimalParabolicMax T hP) K) :=
    (source_component_simple_image T hP hs K hK hgen).2.1.2
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    have hi : Function.Injective c.toMonoidHom := by
      have ho : Odd (Nat.card c.toMonoidHom.ker) := Nat.not_even_iff_odd.mp (by
        rw [even_iff_two_dvd]
        exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
          (pCore_quotient_pCore_eq_bot 2) _ c.ker_le_center)
      exact c.toMonoidHom.ker_eq_bot_iff.mp
        (c.ker_eq_bot_of_odd_of_odd_primeRank_le_one ho (marked_rank_one_odd_ranks _ _ hm))
    exact c.toCovering.ker_eq_center_of_isSimple.symm.trans
      (c.toMonoidHom.ker_eq_bot_iff.mpr hi)
  have hza : center (K.map (QuotientGroup.mk' (pCore 2 H))) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [← Nat.card_congr (centerCongr (cComponentTwoCoreQuotientEquiv hK)).toEquiv,hz]
    simp
  have hcore : ChapterB.minimalParabolicCore T hP = pCore 2 H := by
    rw [hza,Subgroup.map_bot] at hc
    exact le_antisymm (by
      simpa only [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hc.2)
      (ChapterB.minimalParabolicTwoCore_le_core T hP)
  refine ⟨?_,hcore,by rw [normalizer_eq_top,inf_top_eq],hK.subgroupOf le_sup_left,?_⟩
  · let := hK.perfect
    apply le_antisymm
    · exact sInf_le ⟨inferInstance,
        isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen⟩
    · let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
      exact le_of_isPerfect_of_solvable_quotient K (pResidual 2 H)
  · rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,d,_⟩ | ⟨m,hm,hf,d,_⟩
    · exact Or.inl ⟨hf,F,hF,hfin,hcard,⟨e.trans d⟩⟩
    · exact Or.inr ⟨m,hm,hf,⟨e.trans d⟩⟩
end CFSG.Quasithin.Chapter14.Section02
