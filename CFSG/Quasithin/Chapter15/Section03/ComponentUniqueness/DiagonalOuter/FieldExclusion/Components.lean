module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.FieldResidual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Selection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.OddCenter
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.Representatives
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Component selection in the field centralizer

The genuine local Sylow subgroup and fusion give the extraspecial order-27
subgroup in C_G(f), by `Transport`. The residual PSL₃(2) and the established
odd-core bound place that residual in the ordinary layer and bound every
component center's three-rank. Given the still outstanding exclusion of
rank-one components, `Selection` constructs the unique positive-three-rank
component. It has rank two, is normal relative to C_G(f), and contains the
field residual.

The marked center and representative-centralizer geometry then prove that
the residual is a component of the selected component's v-centralizer,
retaining its actual PSL₃(2) equivalence. `Centralizer` proves the complete
relative-centralizer alternative from the remaining cover and odd-center
model facts, including uniqueness of its subgroup of order three.

The two assembly theorems below are explicitly conditional on rank-one
exclusion. That automorphism argument and the three-model identification
are not proved here yet. No source theorem or final field contradiction is
claimed. The SQTK input uses the full known-simple catalogue.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137; Theorem C on p.33, A.3.8 on p.45, A.3.18 on
pp.51--52, and I.3.1--2 on pp.414--415.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

/-- Conditional selection in the source SQTK field centralizer. Only the
rank-one exclusion remains an extra component-theoretic premise. -/
theorem selected_ambient_component_of_fusion_and_rank_exclusion
    (V I L : Subgroup G) [IsKleinFour V]
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hI : I = normalizer (V : Set G)) {w f : G}
    (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eO : pPrimeCore 2 (I ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eF : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hbalance : fieldResidual L f ≤
      oddExtendedTwoComponentLayer (centralizer ({f} : Set G)))
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer ({f} : Set G)))
    (hno : ∀ J : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) J → primeRank 3 J ≠ 1) :
    ∃ K : Subgroup G, K ≤ centralizer ({f} : Set G) ∧
      IsComponent (centralizer ({f} : Set G))
        (K.subgroupOf (centralizer ({f} : Set G))) ∧
      (K.subgroupOf (centralizer ({f} : Set G))).Normal ∧ primeRank 3 K = 2 ∧
      fieldResidual L f ≤ K.subgroupOf (centralizer ({f} : Set G)) ∧
      ∀ J : Subgroup (centralizer ({f} : Set G)),
        IsComponent (centralizer ({f} : Set G)) J → 0 < primeRank 3 J →
          J = K.subgroupOf (centralizer ({f} : Set G)) := by
  let H := centralizer ({f} : Set G)
  have hrank : primeRank 3 H ≤ 2 := hH.stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨ι, hι⟩ := centralizer_oddCore_embeds_of_fusion V I hV hI hw hfusion eO
  let : IsSimpleGroup (fieldResidual L f) := (MulEquiv.isSimpleGroup_congr
    (fieldResidualEquivModel L f eF)).mpr (Atlas.psl_simple_high_rank 3 (by decide))
  let := fieldResidual_perfect L f eF
  have hOr := oddCore_rank_le_one_of_simple_subgroup (fieldResidual L f)
    (fieldResidual_card L f eF) hrank ι hι
  have hF := fieldResidual_le_layer_of_fusion V I L hV hI hw hfusion eO eF hbalance
  obtain ⟨J, hJ, hn, hr, hFJ, hu⟩ := selected_component_of_rank_conditions L f eF hF hrank
    hno (fun J hJ => component_center_rank_le_one_of_oddCore hOr hJ)
  let K := J.map H.subtype
  have he : K.subgroupOf (centralizer ({f} : Set G)) = J := comap_map_eq_self_of_injective H.subtype_injective J
  refine ⟨K, map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using hJ
  · simpa only [he] using hn
  · exact (primeRank_equiv 3 (J.equivMapOfInjective H.subtype H.subtype_injective)).symm.trans hr
  · simpa only [he] using hFJ
  · simpa only [he] using hu

/-- Attach the actual representative-centralizer component to the selected
ambient component. The centralizer bound comes from the preceding geometry;
normality of the residual is proved by characteristicity and conjugation. -/
theorem selected_component_with_representative_of_fusion_and_rank_exclusion
    (V ZS S I L : Subgroup G) [IsKleinFour V]
    (r : CoverReduction.GlobalGeometry.RepresentativeGeometry V ZS S I)
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G)) (hZ : (center L).map L.subtype = V)
    {w f : G} (hfS : f ∈ S)
    (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eO : pPrimeCore 2 (I ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eF : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hbalance : fieldResidual L f ≤
      oddExtendedTwoComponentLayer (centralizer ({f} : Set G)))
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer ({f} : Set G)))
    (hno : ∀ J : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) J → primeRank 3 J ≠ 1) :
    r.v ∈ centralizer ({f} : Set G) ∧
    ∃ K : Subgroup G, K ≤ centralizer ({f} : Set G) ∧
      IsComponent (centralizer ({f} : Set G))
        (K.subgroupOf (centralizer ({f} : Set G))) ∧
      (K.subgroupOf (centralizer ({f} : Set G))).Normal ∧ primeRank 3 K = 2 ∧
      fieldResidual L f ≤ K.subgroupOf (centralizer ({f} : Set G)) ∧
      let A := (fieldResidual L f).map (centralizer ({f} : Set G)).subtype
      let C := K ⊓ centralizer ({r.v} : Set G)
      A ≤ C ∧ (A.subgroupOf C).Normal ∧ IsComponent C (A.subgroupOf C) ∧
        Nonempty ((A.subgroupOf C) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hvH : r.v ∈ centralizer ({f} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (r.sylow_centralizes hfS)).symm
  obtain ⟨K, hKH, hK, hn, hr, hFK, _⟩ :=
    selected_ambient_component_of_fusion_and_rank_exclusion V I L hV hI hw hfusion eO eF
      hbalance hH hno
  have hvV : r.v ∈ V := by
    have h := mem_zpowers r.v
    rw [r.generator] at h
    exact h.2
  obtain ⟨hAC, hAN, hAcomp⟩ :=
    fieldResidual_component_of_marked_center I L K V f r.v hIL r.centralizer_le hZ hvV
      hKH hFK eF
  let eA := (fieldResidual L f).equivMapOfInjective
    (centralizer ({f} : Set G)).subtype (centralizer ({f} : Set G)).subtype_injective
  exact ⟨hvH, K, hKH, hK, hn, hr, hFK, hAC, hAN, hAcomp,
    ⟨(subgroupOfEquivOfLe hAC).trans (eA.symm.trans (fieldResidualEquivModel L f eF))⟩⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
