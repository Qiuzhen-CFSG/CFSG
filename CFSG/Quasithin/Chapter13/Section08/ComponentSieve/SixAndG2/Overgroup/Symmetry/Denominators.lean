module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry.Marking

/-!
# Denominator symmetry and endpoint escape in case (1)

For an asymmetric critical pair, the earlier module alternatives place its
nontrivial transvection center in the original plane. The source square
conjugator from `Marking` contradicts the asymmetric configuration. The cover
alternative uses the same source natural flag. Reversing the critical pair
then proves the equivalence of strictness of the two denominators.

The actual case-(1) disjunction therefore makes both denominators full. F.9.16
supplies the transvection action, and `Fusion` proves the endpoint escapes Q_H.
Only the earlier module alternatives of 13.8.5/13.7.6 remain explicit; their
source discharge belongs to `qt-d-138-six-g2-source`. In particular neither a
marked plane transport nor the symmetry or escape conclusion is assumed.

Source: Aschbacher--Smith, 13.8.7 and 13.8.27(3), pp.948--949,963.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]
/-- The oriented impossibility in 13.8.7, with its earlier source inputs
explicit. In particular neither symmetry nor a line conjugator is assumed. -/
private theorem no_asymmetric
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (c : CriticalPair L (T : Subgroup G) H V) (M₀ : Subgroup G) (z : V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)]
    [((zpowers (z : G)).subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) (zpowers (z : G)))
    (hH : H = centralizer ({(z : G)} : Set G))
    (hcard : Nat.card (zpowers (z : G)) = 2)
    (hpoint : V₁ = zpowers (z : G))
    (hZ₂ : zpowers (z : G) ≤ V₂) (hZ₃ : zpowers (z : G) ≤ V₃)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G))
    (hM : normalizer (zpowers (z : G)) ⊓ normalizer V₃ ≤ M₀)
    (a : CoverGeometry.NaturalAction M₀ V)
    (f : CoverGeometry.NaturalFlag a (T : Subgroup G) (zpowers (z : G)) V₃)
    (hLV : L ≤ normalizer V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l (z : G) = x)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ zpowers (z : G))
    (hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers (z : G))
    (hVHend : Source.VH H V ≤ vertexGroup L (T : Subgroup G) H c.gamma)
    (hVγH : c.Vgamma ≤ H)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hdisj : zpowers (z : G) ⊓ c.Aone (zpowers (z : G)) = ⊥)
    (hcross : ⁅Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))),
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G))⁆ = ⊥)
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ (zpowers (z : G))))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ (zpowers (z : G)))) :
    ¬ (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) <
        Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) = c.Ugamma V₃) := by
  rintro ⟨hstrict, hfull⟩
  have hUV : Source.UH H V₃ ≤ Source.VH H V :=
    conjugateSpanBy_mono f.hyperplane_le le_rfl
  have hγH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans hVγH
  have hHN : H ≤ normalizer (zpowers (z : G)) := by
    intro h hh
    exact mem_normalizer_iff_map_conj_eq.mpr
      (CoverGeometry.fixes_central_line H (z : G) h hH hh)
  have cfg := CoverGeometry.Configuration.of_criticalPair c V₃ (zpowers (z : G))
    hcard (hγH.trans hHN) hstrict hfull hDH hDγ hdisj (hUV.trans hVHend) hcross
  have hAsize : Nat.card (centerAlpha c (zpowers (z : G))) = 2 := by
    change Nat.card ((zpowers (z : G)).map _) = 2
    rw [card_map_of_injective (MulAut.conj (returnElement c : G)).injective, hcard]
  have hdis : zpowers (z : G) ⊓ centerAlpha c (zpowers (z : G)) = ⊥ := by
    rw [inf_comm]
    exact cfg.disjoint
  have ht := transvection_actor_of_commutator Q cfg.in_H cfg.commutator_eq hAsize hdis
  rcases hmodels ht with hirred | hcover
  · have hAU : centerAlpha c (zpowers (z : G)) ≤ Source.UH H V₃ := by
      change (zpowers (z : G)).conjBy (returnElement c : G) ≤ Source.UH H V₃
      rw [← cfg.commutator_eq]
      exact le_normalizer_iff_commutator_le_left.mp (cfg.in_H.trans Q.normalizes)
    have hcenter := nontrivialCenter_of_commutator Q cfg.in_H cfg.commutator_eq hAsize hdis
    have hplace : ∃ h ∈ H, (centerAlpha c (zpowers (z : G))).conjBy h ≤ V₂ := by
      rcases hirred with hlinear | hsix | ⟨N, hmarked⟩
      · obtain ⟨N⟩ := hlinear
        exact Q.place_of_nonzero_transitive N
          CenterQuotientAction.linear_nonzero_transitive _ V₂ hAU hAsize cfg.disjoint hZ₂ b hb hbZ
      · obtain ⟨N⟩ := hsix
        exact Q.place_of_nonzero_transitive N
          SixCenterGeometry.nonzero_transitive _ V₂ hAU hAsize cfg.disjoint hZ₂ b hb hbZ
      · exact place_seven_center Q N _ V₂ hAU hAsize hcenter hZ₂ b hb hmarked
    obtain ⟨h, hh, hplace⟩ := hplace
    have hsize : Nat.card ((centerAlpha c (zpowers (z : G))).conjBy h) = 2 := by
      change Nat.card ((centerAlpha c (zpowers (z : G))).map _) = 2
      rw [card_map_of_injective (MulAut.conj h).injective, hAsize]
    obtain ⟨l, _, hline, hsquare⟩ := square_conjugator d _ z hH hpoint hplace hsize
    rw [hpoint] at hline
    have hz1 : (z : G) ≠ 1 := by
      intro he
      rw [he] at hcard
      simp at hcard
    exact no_asymmetric_pair_of_center_conjugator H V₃ (z : G) (returnElement c : G)
      h l hH hz1 hcard hh hline hsquare cfg.inside cfg.outside
  · obtain ⟨d⟩ := hcover
    exact no_asymmetric_cover L H (T : Subgroup G) V V₃ M₀ (z : G) (returnElement c : G)
      d hH hcard hZ₃ hM a f hLV htrans hHC hQ
      (return_conjugate_le_H c _ hVHend) cfg (returnElement c).property

open CriticalGeometry.Reorientation

/-- The full equivalence of 13.8.7 under H=G₁=C_G(z), with V₁=⟨z⟩.
The reverse critical pair is constructed inside this proof. -/
private theorem strict_iff
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (c : CriticalPair L (T : Subgroup G) H V) (M₀ : Subgroup G) (z : V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)]
    [((zpowers (z : G)).subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) (zpowers (z : G)))
    (hH : H = centralizer ({(z : G)} : Set G))
    (hcard : Nat.card (zpowers (z : G)) = 2)
    (hpoint : V₁ = zpowers (z : G))
    (hZ₂ : zpowers (z : G) ≤ V₂) (hZ₃ : zpowers (z : G) ≤ V₃)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G))
    (hM : normalizer (zpowers (z : G)) ⊓ normalizer V₃ ≤ M₀)
    (a : CoverGeometry.NaturalAction M₀ V)
    (f : CoverGeometry.NaturalFlag a (T : Subgroup G) (zpowers (z : G)) V₃)
    (hLV : L ≤ normalizer V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l (z : G) = x)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ zpowers (z : G))
    (hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers (z : G))
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ (zpowers (z : G))))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ (zpowers (z : G))))
    (hgeo : ∀ d : CriticalPair L (T : Subgroup G) H V, EarlierGeometry d V₃ (zpowers (z : G))) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) < Source.UH H V₃ ↔
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) < c.Ugamma V₃ := by
  have hno (e : CriticalPair L (T : Subgroup G) H V) := no_asymmetric d e M₀ z Q hH hcard hpoint hZ₂ hZ₃ b hb hbZ hM a f hLV htrans hHC hQ
    (hgeo e).VH_endpoint (hgeo e).Vgamma_H (hgeo e).DH_kernel
    (hgeo e).Dgamma_kernel (hgeo e).lines_disjoint (hgeo e).cross_centralizes hmodels
  have hZ : H ≤ normalizer (zpowers (z : G)) := by
    intro h hh
    exact mem_normalizer_iff_map_conj_eq.mpr
      (CoverGeometry.fixes_central_line H (z : G) h hH hh)
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono f.hyperplane_le le_rfl
  have hγH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans (hgeo c).Vgamma_H
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone (zpowers (z : G))) := by
    have hn := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hZ
    rw [map_equiv_normalizer_eq] at hn
    rw [← c.vertexGroup_gamma] at hn
    exact (hUV.trans (hgeo c).VH_endpoint).trans hn
  constructor
  · intro hs
    by_contra hn
    have he := eq_of_le_of_not_lt (commutatorPreimage_le (c.Ugamma V₃)
      (Source.UH H V₃) (zpowers (z : G))) hn
    exact hno c ⟨hs, he⟩
  · intro hs
    by_contra hn
    have he := eq_of_le_of_not_lt (commutatorPreimage_le (Source.UH H V₃)
      (c.Ugamma V₃) (c.Aone (zpowers (z : G)))) hn
    obtain ⟨r⟩ := exists_reversal_of_strict c V₃ (zpowers (z : G))
      (hgeo c).length f.hyperplane_le (hgeo c).Vgamma_H hZ (hgeo c).first_kernel hs
    exact hno r.pair (reverse_asymmetry r V₃ (zpowers (z : G)) hZ hγH hUA he hs)


open TransvectionRecognition.Component.ModelExtension

/-- The symmetry theorem on the original source action and flag. The only
module input is the earlier equivariant model alternative of 13.8.5/13.7.6. -/
theorem source_strict_iff
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (Q : letI := d.uh_elementary hHz
      CenterQuotientAction H (Source.UH H V₃) V₁)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ V₁)
    (hmodels : letI := d.uh_elementary hHz
      (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ V₁)) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ↔
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  have hzexists : ∃ zv : V, V₁ = zpowers (zv : G) := by
    obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
    have hzG : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
    have hzV : (z : G) ∈ V :=
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z.property
    exact ⟨⟨z.val, hzV⟩,
      CenterQuotientAction.line_eq_zpowers V₁ d.line_card z hzG⟩
  obtain ⟨zv, hp⟩ := hzexists
  subst V₁
  let : IsElementaryAbelian 2 V := hF9.elementary
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  have hcard : Nat.card (zpowers (zv : G)) = 2 := d.line_card
  have hzG : (zv : G) ≠ 1 := by
    intro he
    rw [he] at hcard
    simp at hcard
  have hHz : H = centralizer ({(zv : G)} : Set G) := by
    rw [hH, d.first_normalizer]
    apply le_antisymm
    · exact normalizer_line_le_centralizer _ hzG hcard
    · intro k hk
      exact mem_normalizer_iff_map_conj_eq.mpr
        (CoverGeometry.fixes_central_line _ (zv : G) k rfl hk)
  obtain ⟨a, f⟩ := natural_flag (localNaturalSetup d)
  have hM : normalizer (zpowers (zv : G)) ⊓ normalizer V₃ ≤
      M ⊓ normalizer V := by
    simpa only [d.first_normalizer] using
      Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
  have hHC := Section07.centralizer_UH_commutator (localNaturalSetup d) hF9
  rw [commutator_comm] at hHC
  have hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers (zv : G) := by
    rw [commutator_comm]
    exact (commutator_mono (le_conjugateSpanBy V₃ H) le_rfl).trans
      hF9.commutator_UH_QH_le_point
  exact strict_iff (localNaturalSetup d) c (M ⊓ normalizer V) zv Q hHz hcard rfl
    d.line_le_plane (d.line_le_plane.trans d.plane_le_seed) b hb hbZ hM a f
    (le_sup_left.trans d.normalizes_V)
    (fun x hx hx1 => local_nonzero_transitive d zv.property hx hzG hx1)
    hHC hQ hmodels (local_earlierGeometry d hF9)


theorem case_one
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (Q : letI := d.uh_elementary hHz
      CenterQuotientAction H (Source.UH H V₃) V₁)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ V₁)
    (hmodels : letI := d.uh_elementary hHz
      (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ V₁))
    (hcase : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    let _ : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃))) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have he := source_strict_iff d hHz hF9 c hH hcentral Q b hb hbZ hmodels
  have hboth : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ := by
    rcases hcase with h | h
    · refine ⟨h, eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) (fun hs => ?_)⟩
      have hh := he.mpr hs
      rw [h] at hh
      exact lt_irrefl _ hh
    · refine ⟨eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) (fun hs => ?_), h⟩
      have hh := he.mp hs
      rw [h] at hh
      exact lt_irrefl _ hh
  obtain ⟨hc, hline, action, happ, hne, ht⟩ :=
    full_denominators_transvections d hHz hF9 c hboth.1 hboth.2
  exact ⟨hboth.1, hboth.2, hc, hline,
    full_denominators_escape d hF9 c hboth.1 hboth.2 hcentral, action, happ, hne, ht⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry
