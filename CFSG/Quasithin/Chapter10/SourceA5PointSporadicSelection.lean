module
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleSelection
public import CFSG.Quasithin.Chapter10.SourceA5PointRudvalisShape
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held

/-!
# The original point inspection excludes M24 and Held

The original local image has nontrivial two-core, with its prescribed full
Sylow normalizing it. The native maximal two-local catalogues put that same
image in the actual octad, sextet or trio geometries for M24, and the three
actual two-local geometries for Held. Their solvable quotients exclude the
A₅ two-core quotient. The native Rudvalis core-center bound then leaves only
J4 after the already proved rank-two and sporadic point calculations.

Source: Aschbacher–Smith A.3.12 and 10.2.9, printed pp.47–48,750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The original center bound rules out the M24 and Held local sections. -/
theorem source_a5_point_not_mathieuTwentyFour_or_held
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hmodel : Nonempty ((I ⧸ center I) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((I ⧸ center I) ≃* Held.He)) : False := by
  obtain ⟨S,_,_,hl,hN,_,⟨eB⟩,h16⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  change 16 ≤ Nat.card (center (pCore 2 B)) at h16
  have hc : pCore 2 B ≠ ⊥ := by
    intro hz
    have hle := (center (pCore 2 B)).card_le_card_group
    have hcard : Nat.card (pCore 2 B) = 1 := by rw [hz,card_bot]
    omega
  rcases hmodel with he | he
  · exact SourceEmbeddings.FiveLocalFF.MathieuTwentyFour.not_section he.some
      (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) B hl hN hc eB
  · exact SourceEmbeddings.FiveLocalFF.Held.not_section he.some
      (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) B hl hN hc eB

/-- Actual source markings leave only the two unresolved J4 and Ru carriers. -/
theorem source_a5_point_quasisimple_marking_or_j4_rudvalis
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    SourceA5PointQuasisimpleMarking.{u,0} L I ∨
      Nonempty ((I ⧸ center I) ≃* Janko4.Model) ∨
      Nonempty ((I ⧸ center I) ≃* Rudvalis.Model) := by
  rcases source_a5_point_quasisimple_marking_or_four_sporadic
    D e hn t hv hvne hvL hv0 hs hLI hIX hI with hm | ⟨name,hnames,he⟩
  · exact Or.inl hm
  · rcases hnames with h24 | hj4 | hhe | hru
    · subst name
      exact (source_a5_point_not_mathieuTwentyFour_or_held
        D e hn hvL hv0 hs hLI hIX hI (Or.inl he)).elim
    · subst name
      exact Or.inr (Or.inl he)
    · subst name
      exact (source_a5_point_not_mathieuTwentyFour_or_held
        D e hn hvL hv0 hs hLI hIX hI (Or.inr he)).elim
    · subst name
      exact Or.inr (Or.inr he)

/-- Every other carrier gives the actual original point-component alternative. -/
theorem source_a5_point_quasisimple_alternative_or_j4_rudvalis
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    SourceA5PointComponentAlternative D e t I ∨
      Nonempty ((I ⧸ center I) ≃* Janko4.Model) ∨
      Nonempty ((I ⧸ center I) ≃* Rudvalis.Model) := by
  rcases source_a5_point_quasisimple_marking_or_j4_rudvalis
    D e hn t hv hvne (hcross hv) hv0 hs hLI hIX hI with hm | he
  · exact Or.inl (source_a5_point_alternative_of_quasisimple_marking
      D e t I hLI.le hv hNI hcross hm)
  · exact Or.inr he

/-- The completed Rudvalis exclusion leaves only the J4 carrier. -/
theorem source_a5_point_quasisimple_marking_or_j4
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    SourceA5PointQuasisimpleMarking.{u,0} L I ∨
      Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  rcases source_a5_point_quasisimple_marking_or_j4_rudvalis
    D e hn t hv hvne hvL hv0 hs hLI hIX hI with hm | hj4 | hru
  · exact Or.inl hm
  · exact Or.inr hj4
  · exact (source_a5_point_not_rudvalis_of_local
      D e hn hvL hv0 hs hLI.le hIX hI hru.some).elim

/-- The original point-component alternative now has only the J4 exception. -/
theorem source_a5_point_quasisimple_alternative_or_j4
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    SourceA5PointComponentAlternative D e t I ∨
      Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  rcases source_a5_point_quasisimple_marking_or_j4
    D e hn t hv hvne (hcross hv) hv0 hs hLI hIX hI with hm | hj4
  · exact Or.inl (source_a5_point_alternative_of_quasisimple_marking
      D e t I hLI.le hv hNI hcross hm)
  · exact Or.inr hj4

end CFSG.Quasithin.Chapter10
