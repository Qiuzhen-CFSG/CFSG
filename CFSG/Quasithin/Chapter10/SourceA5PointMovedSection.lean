module
public import CFSG.Quasithin.Chapter10.SourceA5PointMovedImage
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Recognition
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.Quotient

/-!
# The chosen original moved section through the containing central quotient

Let W=[D.fullModule,L], and take its literal image E in I/Z(I), together
with the image B of L. The original irreducible action on W/C_W(L) gives
the invariant-subgroup interval between C_E(B) and E. Pull an invariant
subgroup in that interval back to W: its preimage contains C_W(L), so the
original interval theorem makes it either the fixed kernel or all of W.
Mapping back proves the required alternative without identifying new quotient
fixed vectors or assuming irreducibility of an entire block.

The actual map L → B has central two-kernel. Consequently O₂(L) maps onto
O₂(B), and the source centralization of the full module by O₂(L) proves
that O₂(B) centralizes E. The final theorem assembles both facts with the
original full point Sylow, elementary cardinality and full movement. These
are precisely the chosen-section inputs to the J₄ first-centralizer argument.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, using the original
chosen irreducibility from 3.2.6 and 10.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
local instance movedSectionElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem original_moved_interval
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (K : Subgroup G) (hz : sourceMovedFixed D ≤ K)
    (hw : K ≤ ⁅D.fullModule,L⁆) (hn : L ≤ normalizer (K : Set G)) :
    K = sourceMovedFixed D ∨ K = ⁅D.fullModule,L⁆ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Representation.IsIrreducible ((originalMovedQuotientAction D e).comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr hi
  exact (originalMovedQuotientSection D e).eq_kernel_or_section K hz hw hn

/-- The chosen irreducible section gives the exact invariant-subgroup interval
on the original moved image in the containing central quotient. -/
theorem source_a5_containing_center_moved_irreducible_interval
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {I : Subgroup G} (hLI : L ≤ I) :
    let q := QuotientGroup.mk' (center I)
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    ∀ K : Subgroup (I ⧸ center I), E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
      B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E := by
  let W := ⁅D.fullModule,L⁆
  let q := QuotientGroup.mk' (center I)
  let E := (W.subgroupOf I).map q
  let B := (L.subgroupOf I).map q
  have hWI : W ≤ I := (source_full_moved_le_component D).trans hLI
  change ∀ K : Subgroup (I ⧸ center I), E ⊓ centralizer (B : Set _) ≤ K → K ≤ E →
    B ≤ normalizer (K : Set _) → K = E ⊓ centralizer (B : Set _) ∨ K = E
  intro K hz hw hn
  let J := (W.subgroupOf I ⊓ K.comap q).map I.subtype
  have hJW : J ≤ W := by
    exact (map_mono inf_le_left).trans (map_subgroupOf_eq_of_le hWI).le
  have hCJ : sourceMovedFixed D ≤ J := by
    intro c hc
    have hcI : c ∈ I := hWI hc.1
    refine mem_map.mpr ⟨⟨c,hcI⟩,⟨hc.1,?_⟩,rfl⟩
    apply hz
    refine ⟨mem_map.mpr ⟨⟨c,hcI⟩,hc.1,rfl⟩,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg q (Subtype.ext (hc.2 l hl))
  have hLJ : L ≤ normalizer (J : Set G) := by
    have h1 : L.subgroupOf I ≤ normalizer (W.subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq hWI]
      exact comap_mono (normalizer_commutator_ge_right _ _)
    have h2 : L.subgroupOf I ≤ normalizer (K.comap q : Set I) :=
      ((map_le_iff_le_comap.mp hn).trans (le_normalizer_comap q))
    have h3 := (le_inf h1 h2).trans inf_normalizer_le_normalizer_inf
    have h4 := (map_mono h3).trans (le_normalizer_map I.subtype)
    rwa [map_subgroupOf_eq_of_le hLI] at h4
  have hJK : (J.subgroupOf I).map q = K := by
    have hpre : J.subgroupOf I = W.subgroupOf I ⊓ K.comap q := by
      exact comap_map_eq_self_of_injective I.subtype_injective _
    rw [hpre]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro x hx
      obtain ⟨w,hwE,he⟩ := hw hx
      exact mem_map.mpr ⟨w,⟨hwE,show q w ∈ K from he.symm ▸ hx⟩,he⟩
  rcases original_moved_interval D e hi J hCJ hJW hLJ with hc | he
  · left
    apply le_antisymm ?_ hz
    refine le_inf hw ?_
    rw [←hJK,hc]
    rintro _ ⟨c,hc,rfl⟩ _ ⟨l,hl,rfl⟩
    exact congrArg q (Subtype.ext (hc.2 l hl))
  · right
    simpa only [he] using hJK.symm

/-- The actual two-core of the local central-quotient image fixes the same
original moved image pointwise. -/
theorem source_a5_containing_center_moved_core_centralizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) :
    let q := QuotientGroup.mk' (center I)
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    B.pCoreIn 2 ≤ centralizer (E : Set (I ⧸ center I)) := by
  let W := ⁅D.fullModule,L⁆
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let B := A.map q
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f : L →* B := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hh
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  have hzc : center L ≤ pCore 2 L := by
    intro z hz
    apply (QuotientGroup.eq_one_iff z).mp
    apply e.injective
    rw [e.map_one]
    have hc : e (QuotientGroup.mk' (pCore 2 L) z) ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
      rw [←hl]
      simpa only [Function.comp_apply,map_mul] using
        congrArg (fun x : L => e (QuotientGroup.mk' (pCore 2 L) x))
          (mem_center_iff.mp hz l)
    rwa [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hk.trans hzc)
  have hcore : (pCore 2 L).map f = pCore 2 B := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let N := (W.subgroupOf L).map f
  have hNc : pCore 2 B ≤ centralizer (N : Set B) := by
    intro b hb
    rw [←hcore] at hb
    obtain ⟨r,hr,rfl⟩ := hb
    rintro _ ⟨w,hw,rfl⟩
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    have hh : w*r=r*w := Subtype.ext
      (source_component_core_centralizes_fullModule D (mem_map_of_mem L.subtype hr)
        w (hWV hw))
    simpa only [map_mul] using congrArg f hh
  have hmap : N.map B.subtype = (W.subgroupOf I).map q := by
    rw [map_map]
    have hcomp : B.subtype.comp f = q.comp (inclusion hLI) := rfl
    rw [hcomp,←map_map]
    congr 1
    apply map_injective I.subtype_injective
    rw [map_map,subtype_comp_inclusion,
      map_subgroupOf_eq_of_le (source_full_moved_le_component D),
      map_subgroupOf_eq_of_le ((source_full_moved_le_component D).trans hLI)]
  change (pCore 2 B).map B.subtype ≤ centralizer ((W.subgroupOf I).map q : Set _)
  rw [←hmap]
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hNc,Subgroup.map_bot]

/-- The original full point Sylow carries all chosen-section data needed by
the native first-centralizer obstruction, on the same literal quotient image. -/
theorem source_a5_point_center_moved_section_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    let q := QuotientGroup.mk' (center I)
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let B := (L.subgroupOf I).map q
    ∃ S : Sylow 2 (I ⧸ center I),
      B ∈ localCComponents S ∧ (S : Subgroup (I ⧸ center I)) ≤ normalizer (B : Set (I ⧸ center I)) ∧
      (S : Subgroup (I ⧸ center I)) ≤ normalizer (E : Set (I ⧸ center I)) ∧
      IsElementaryAbelian 2 E ∧ E ≤ B ∧ 16 ≤ Nat.card E ∧
      B.pCoreIn 2 ≤ centralizer (E : Set (I ⧸ center I)) ∧ ⁅E,B⁆ = E ∧
      ∀ K : Subgroup (I ⧸ center I), E ⊓ centralizer (B : Set (I ⧸ center I)) ≤ K → K ≤ E →
        B ≤ normalizer (K : Set (I ⧸ center I)) → K = E ⊓ centralizer (B : Set (I ⧸ center I)) ∨ K = E := by
  obtain ⟨S,hSm,_,hl,hSB,_,_,_⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  obtain ⟨hE,hcard⟩ := source_a5_containing_center_moved_elementary_card D e hLI.le
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective (center I)),hl,hSB,
    source_a5_point_center_moved_normalized D hn hvL hv0 hLI.le S hSm,
    hE,map_mono (comap_mono (source_full_moved_le_component D)),hcard,
    source_a5_containing_center_moved_core_centralizes D e hLI.le,
    source_a5_containing_center_moved_commutator D hLI.le,
    source_a5_containing_center_moved_irreducible_interval D e hi hLI.le⟩

end CFSG.Quasithin.Chapter10
