module
public import CFSG.Quasithin.Chapter10.SourceA5PointCarrierData
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve

/-!
# The actual quasisimple point carrier is rank two or sporadic

The original point vector is an involution. Its containing component therefore
has the proved Theorem C simple central quotient. The same full point Sylow
retains the original proper local component and A₅ two-core quotient. The
original moved module supplies an elementary subgroup of order at least sixteen.
The concrete carrier sieve removes the alternating, odd, Bender and higher
binary-linear rows, leaving only the rank-two and sporadic rows for marking.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, and A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Carrier pruning uses the literal original local subgroup and moved module. -/
theorem source_a5_point_center_quotient_rank_two_or_sporadic
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
    (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) f) ∨
      ChapterA.Section02.IsTheoremCSporadicModel (I ⧸ center I) := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsQuasisimple (I ⧸ center I) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center I)) (QuotientGroup.mk'_surjective (center I))
  have hm := source_a5_point_center_quotient_theoremC_model D t hv hvne hIX
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  obtain ⟨E,_,hE,h16⟩ := source_a5_containing_center_image_elementary D e hLI.le
  exact SourceEmbeddings.FiveLocalFF.CarrierSieve.rank_two_or_sporadic
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I)))
    ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) hl hp eB E hE h16 hm

/-- Original Sylow normalization reduces the sporadic branch to six actual carriers. -/
theorem source_a5_point_center_quotient_six_sporadic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (I ⧸ center I)) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .he ∨ name = .ru) ∧ Nonempty ((I ⧸ center I) ≃* name.Carrier) := by
  obtain ⟨S,hSm,_,_⟩ := source_point_containing_component_local_sylow
    D hn hvL hv0 hs hLI hIX hI
  obtain ⟨hE,h16⟩ := source_a5_containing_center_moved_elementary_card D e hLI
  exact SourceEmbeddings.FiveLocalFF.SporadicSieve.six_carriers
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I)))
    (((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I))) hE
    (source_a5_point_center_moved_normalized D hn hvL hv0 hLI S hSm) h16 hm

/-- The original source data leave rank two and the six remaining sporadic carriers. -/
theorem source_a5_point_center_quotient_carriers
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
    (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) f) ∨
      ∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
          name = .he ∨ name = .ru) ∧ Nonempty ((I ⧸ center I) ≃* name.Carrier) := by
  rcases source_a5_point_center_quotient_rank_two_or_sporadic
    D e hn t hv hvne hvL hv0 hs hLI hIX hI with hr | hs'
  · exact Or.inl hr
  · exact Or.inr (source_a5_point_center_quotient_six_sporadic D e hn hvL hv0 hs hLI.le hIX hI hs')

end CFSG.Quasithin.Chapter10
