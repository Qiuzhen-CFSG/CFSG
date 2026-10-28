module

public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.GroupTheory.SylowSubnormalIntersection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings

/-!
# The rank-one non-enlargement branch of A.3.12

Intersect the original full Sylow with the containing C-component L. The
smaller local C-component B remains a C-component after adjoining only that
intersection. This join is nonsolvable, so the rank-one Sylow-overgroup
calculation makes it all of L. C-component minimality then gives B = L.

The last theorem applies this argument after the literal quotient by the
ambient two-core. It concludes equality of the actual images, without
identifying subgroups that could have different solvable radicals. The
containing component and its rank-one model are the preceding source inputs;
neither invariance nor an embedding alternative for B is assumed.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and its application in
2.4.6, printed p.528 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Restrict the source local family using the actual full Sylow intersection.
An independent proper-Sylow-overgroup calculation suffices for non-enlargement. -/
theorem eq_of_solvable_sylow_overgroups
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hproper : ∀ (S : Sylow 2 L) (P : Subgroup L),
      (S : Subgroup L) ≤ P → P ≠ ⊤ → Group.IsSolvable P) : B = L := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  let J := B ⊔ (S : Subgroup L).map L.subtype
  have hSL : (S : Subgroup L).map L.subtype ≤ L := map_subtype_le _
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS, subgroupOf_map_subtype]
    exact inf_le_left
  have hJL : J ≤ L := sup_le hBL hSL
  have hBJ : (B.subgroupOf J).IsCComponent :=
    hB.subgroupOf_of_le le_sup_left (sup_le le_sup_left (hST.trans le_sup_right))
  have hJns : ¬ Group.IsSolvable J := by
    intro hs
    let := hs
    exact hBJ.not_isSolvable inferInstance
  have htop : J.subgroupOf L = ⊤ := by
    by_contra hne
    let := hproper S (J.subgroupOf L) (by
      intro s hs
      exact (show (S : Subgroup L).map L.subtype ≤ J from le_sup_right)
        (mem_map_of_mem L.subtype hs)) hne
    exact hJns (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hJL).toMonoidHom) (subgroupOfEquivOfLe hJL).surjective)
  have he : J = L := le_antisymm hJL (subgroupOf_eq_top.mp htop)
  rw [he] at hBJ
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hBJ))

/-- Genuine A.3.12 non-enlargement for a rank-one C-component cover.
The containing component has its actual two-core quotient and actual SL₂ map. -/
theorem eq_of_rankOne_cover
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (f : L →* SL(2, F)) (hf : Function.Surjective f) : B = L := by
  let := hL.perfect
  have htop : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.subgroupOf le_rfl
  apply eq_of_solvable_sylow_overgroups T hB hL hBL
  intro S P hSP hne
  by_contra hns
  exact hne (Matrix.SpecialLinearGroup.sylow_overgroup_eq_top_of_component_cover
    htop f hf S P hSP hns)

/-- The complete A.3.12 output in the rank-one containing-component branch:
the first alternative, including its original uniqueness assertion. -/
theorem conclusion_of_rankOne_cover
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (f : L →* SL(2, F)) (hf : Function.Surjective f) :
    Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_rankOne_cover T hB hL hBL f hf
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm

/-- Apply the source branch to the literal images in G/O₂(G), as required
by 1.2.4 and the block non-enlargement argument in 2.4.6. -/
theorem twoCore_images_eq_of_rankOne_cover
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple ((L.map (QuotientGroup.mk' (pCore 2 G))) ⧸
      pCore 2 (L.map (QuotientGroup.mk' (pCore 2 G))))]
    (f : L.map (QuotientGroup.mk' (pCore 2 G)) →* SL(2, F))
    (hf : Function.Surjective f) :
    B.map (QuotientGroup.mk' (pCore 2 G)) =
      L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply eq_of_rankOne_cover
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) f hf
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
