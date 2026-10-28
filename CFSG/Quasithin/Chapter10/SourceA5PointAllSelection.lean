module
public import CFSG.Quasithin.Chapter10.SourceA5PointSporadicSelection
public import CFSG.Quasithin.Chapter10.SourceA5PointAllLocalLie
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
public import CFSG.Quasithin.Chapter10.SourceA5PointMovedSection

/-!
# Quasisimple point inspection for every original vector

The actual point Sylow stabilizes L whenever the point centralizer escapes
its prescribed maximal subgroup, including vectors fixed by the whole local
orbit. That stabilization supplies the literal local image and normalized
moved subgroup in I/Z(I). The complete carrier sieve, native local placements
and chosen irreducible section then give a marked source row without a
separate embedding premise. The excluded sporadic rows use that same image.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, with the covering-uniqueness
replacement for the fixed-vector reduction.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
local instance allSelectionMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem rank_two_marking_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  cases hm with
  | linear hf hm =>
    exact (source_a5_point_linear_three_model_marking_of_normalizes
      D e hstab hs hLI hIX hI hf hm).2
  | symplectic hf hm =>
    exact (source_a5_point_symplectic_model_marking_of_normalizes
      D e hstab hs hLI hIX hI hf hm).2
  | g2 hf hm =>
    exact (source_a5_point_g2_model_marking_of_normalizes
      D e hstab hs hLI hIX hI hf hm).2
  | triality hf hm =>
    obtain ⟨eI⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
      (I ⧸ center I) n (by omega)).mp hm
    obtain ⟨S,_,_,hl⟩ :=
      source_point_containing_component_local_sylow_of_normalizes D hstab hs hLI.le hIX hI
    obtain ⟨hq,f,hf⟩ := source_a5_triality_local_image_marking D e hLI.le S hl n (by omega) eI
    exact .triality n (by omega) hq f (Or.inr hf)
  | ree_f4 m hm _ he =>
    exact (source_a5_not_ree_containing_quotient D e hLI.le hm he.some).elim
  | symplectic_derived _ he =>
    exact (source_a5_not_symplectic_binary_containing_quotient D e hLI.le he.some).elim
  | g2_derived _ he =>
    exact (source_a5_not_g2_binary_containing_quotient e hLI.le (by simp) he.some).elim
  | tits _ he =>
    exact (source_a5_not_tits_containing_quotient D e hLI.le he.some).elim

/-- Full Sylow stabilization and the chosen original section discharge every
carrier and marking premise in the actual quasisimple point inspection. -/
theorem source_a5_point_quasisimple_marking_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsQuasisimple (I ⧸ center I) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center I)) (QuotientGroup.mk'_surjective (center I))
  have hm := source_a5_point_center_quotient_theoremC_model D t hv hvne hIX
  obtain ⟨S,hSm,_,hl,hSB,hp,⟨eB⟩,h16⟩ :=
    source_a5_point_center_quotient_local_embedding_of_normalizes D e hstab hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hE,hcard⟩ := source_a5_containing_center_moved_elementary_card D e hLI.le
  have hSE := source_a5_point_center_moved_normalized_of_normalizes D hstab hLI.le S hSm
  have hBcore : pCore 2 B ≠ ⊥ := by
    change 16 ≤ Nat.card (center (pCore 2 B)) at h16
    intro hz
    have hle := (center (pCore 2 B)).card_le_card_group
    have hcard : Nat.card (pCore 2 B) = 1 := by rw [hz,card_bot]
    omega
  rcases SourceEmbeddings.FiveLocalFF.CarrierSieve.rank_two_or_sporadic
    Sbar B hl hp eB E hE hcard hm with ⟨n,hrank⟩ | hspor
  · exact rank_two_marking_of_normalizes D e hstab hs hLI hIX hI hrank
  · obtain ⟨name,hnames,he⟩ :=
      SourceEmbeddings.FiveLocalFF.SporadicSieve.six_carriers Sbar E hE hSE hcard hspor
    rcases hnames with h22 | h23 | h24 | hj4 | hhe | hru
    · subst name
      obtain ⟨hcore,hc⟩ := source_a5_m22_normalized_image_core_shape he.some Sbar hSB eB
      obtain ⟨f,hf⟩ := source_a5_m22_local_image_exists_marking he.some Sbar hl hcore hc eB
      exact .mathieu22 f hf
    · subst name
      exact .mathieu23 he.some
    · subst name
      exact (SourceEmbeddings.FiveLocalFF.MathieuTwentyFour.not_section
        he.some Sbar B hl hSB hBcore eB).elim
    · subst name
      exact (SourceEmbeddings.FiveLocalFF.JankoFour.not_section he.some Sbar B E
        hl hSB eB hBcore hSE hE (map_mono (comap_mono (source_full_moved_le_component D)))
        hcard (source_a5_containing_center_moved_core_centralizes D e hLI.le)
        (source_a5_containing_center_moved_commutator D hLI.le)
        (source_a5_containing_center_moved_irreducible_interval D e hi hLI.le)).elim
    · subst name
      exact (SourceEmbeddings.FiveLocalFF.Held.not_section
        he.some Sbar B hl hSB hBcore eB).elim
    · subst name
      exact (source_a5_not_rudvalis_normalized_image D e hLI.le he.some Sbar hSB).elim

end CFSG.Quasithin.Chapter10
