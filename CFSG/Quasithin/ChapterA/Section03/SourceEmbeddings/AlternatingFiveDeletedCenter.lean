module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedContaining
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.TwoQuotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The deleted-five block in the simple central quotient

The kernel on the actual block is central and lies in its two-core. The
central two-quotient theorem therefore preserves the deleted module. The
full Sylow and local-component markings descend through the literal quotient,
and perfectness prevents the proper block from becoming the whole quotient.
Theorem A supplies strong quasithinness of this semisimple section, so Theorem C
classifies that same simple quotient.

Source: Aschbacher–Smith A.3.14 and 10.2.1, printed pp.49–50,743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] [IsQuasisimple G]

/-- All local markings of the proper deleted block descend through the center. -/
theorem alternatingFive_block_center_image
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hblock : IsAlternatingBlock B 5) (hne : B ≠ ⊤) :
    let q := QuotientGroup.mk' (center G)
    let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
    B.map q ∈ localCComponents T ∧
    (T : Subgroup (G ⧸ center G)) ≤ normalizer (B.map q : Set _) ∧
    IsAlternatingBlock (B.map q) 5 ∧ B.map q ≠ ⊤ := by
  intro q T
  let f := q.subgroupMap B
  have hfc : f.ker ≤ center B := by
    intro b hb
    have hz : (b : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_center_iff.mp hz a)
  have hfp : IsPGroup 2 f.ker := by
    apply pCore_isPGroup.to_le
    exact hfc.trans ((center_le_centralizer _).trans_eq hblock.2.1.centralizer_blockU)
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (center G)).ker
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  refine ⟨localCComponents_map_of_solvable_ker hB q,
    (map_mono hSB).trans (le_normalizer_map q),
    hblock.of_surjective_central_two_kernel f (q.subgroupMap_surjective B) hfp hfc,?_⟩
  intro ht
  apply hne
  apply eq_top_of_sup_center_eq_top B
  have hh := congrArg (Subgroup.comap q) ht
  simpa only [Subgroup.comap_map_eq,q,QuotientGroup.ker_mk',Subgroup.comap_top] using hh

/-- The actual simple central quotient has the full source C model catalogue. -/
theorem quasisimple_center_quotient_theoremC_model
    (hG : IsSQTK KnownSimple.IsKnownSimple G) :
    ChapterA.Section02.IsTheoremCModel (G ⧸ center G) := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  have hsemiG : componentLayer G = ⊤ := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup G).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple (G ⧸ center G) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _) hsemiG
  have hsec : ChapterA.Section02.IsSectionOf (G ⧸ center G) G :=
    ChapterA.Section02.IsSectionOf.of_surjective _
      (QuotientGroup.mk'_surjective (center G))
  have hq := ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    hG.stronglyQuasithin hG.isKGroup hsec hsemi
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hq (hG.isKGroup.quotient _)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
