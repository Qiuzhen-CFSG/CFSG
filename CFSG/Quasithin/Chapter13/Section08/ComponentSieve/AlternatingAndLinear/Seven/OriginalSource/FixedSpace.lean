module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticEquality
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SevenPointInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport
public import Theory.Representation.BinaryOffender.SaturatedCodimension

/-!
# The full source fixed space and the terminal A₇ contradiction

Equality in F.9.16 makes the fixed-codimension bound on the critical
denominator exact. Every fixed vector therefore lifts into D_H. Its
commutators belong to both V₁ and A₁; the actual disjointness of these lines
makes that lift centralize Uγ. This identifies the full fixed space with
the image of the literal group centralizer.

Conjugating the proved 13.7.3(7) bound now controls displacement under Vγ
on the whole fixed space. The final theorem applies it to the original
submodule and quotient, constructs both natural embeddings, and closes
the rank-one terminal contradiction. The two partition cases still have
to produce rank one and noncentrality on the submodule; the earlier F.9
hypothesis and component supplement retain their source assembly owners.
No displacement, recognition, or centralizer conclusion is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.7.3(7) and 13.8.23–24, printed pp.958–959 (PDF pp.975–976),
combined manuscript, 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open SourceCompletion CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_fixedSpace_eq_centralizer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcmp : Reorientation.denominatorRank V₃ V₁ c ≤
      rank (Source.starImage H (c.Ugamma V₃)))
    (he : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) =
      2 * rank (Source.starImage H (c.Ugamma V₃))) :
    s.image (Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G)) =
      fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  let : IsElementaryAbelian 2
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH :=
    inferInstanceAs (IsElementaryAbelian 2 (Source.UH H V₃))
  let A := Source.starImage H (c.Ugamma V₃)
  let D := Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)
  have hg := local_earlierGeometry d hF9 c
  have hUgH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := starImage_isElementaryAbelian H (c.Ugamma V₃) hUgH
  obtain ⟨N, hN, hZ, hdisp, hfix⟩ := f9_denominator_action _ hF9 c hg.length s
  change Subrepresentation (ρ.comp A.subtype) at N
  change N.toSubmodule = s.image D at hN
  change Module.finrank (ZMod 2) (s.image (c.Aone V₁)) ≤ 1 at hZ
  change ∀ b : A, ∀ v ∈ N.toSubmodule, ρ b v - v ∈ s.image (c.Aone V₁) at hdisp
  change ∀ b : A, ∀ z ∈ s.image (c.Aone V₁), ρ b z = z at hfix
  have hcodim : fixedCodim (ρ.comp A.subtype) ⊤ = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, A.range_subtype]
  have hdenom : Module.finrank (ZMod 2) (E ⧸ N.toSubmodule) =
      Reorientation.denominatorRank V₃ V₁ c := by
    rw [hN]
    exact s.quotient_finrank D (s.line_le_DH _ _ hUgH)
  have hsmall := CommonCenter.fixedCodim_top_le_of_center_dim_le_one N.toRepresentation
    ((s.image (c.Aone V₁)).comap N.toSubmodule.subtype)
    (by
      have hh : Module.finrank (ZMod 2)
          ((s.image (c.Aone V₁)).comap N.toSubmodule.subtype) =
          Module.finrank (ZMod 2) (N.toSubmodule ⊓ s.image (c.Aone V₁) : Submodule (ZMod 2) E) := by
        rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
      exact hh.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ))
    (fun a v => hdisp a v v.property)
    (fun a z hz => Subtype.ext (hfix a z hz))
  have hloss := fixedCodim_le_subrepresentation_add_codim (ρ.comp A.subtype) N ⊤
  have hsat : fixedCodim (ρ.comp A.subtype) ⊤ = fixedCodim N.toRepresentation ⊤ +
      Module.finrank (ZMod 2) (E ⧸ N.toSubmodule) := by
    change fixedCodim N.toRepresentation ⊤ ≤ rank A at hsmall
    rw [hcodim] at hloss ⊢
    change fixedCodim ρ A = 2 * rank A at he
    change Reorientation.denominatorRank V₃ V₁ c ≤ rank A at hcmp
    rw [hdenom] at hloss ⊢
    omega
  have hfixedD : fixedSpace ρ A ≤ s.image D := by
    have hh := fixedSpace_le_of_saturated_codimension (ρ.comp A.subtype) N ⊤ hsat
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, A.range_subtype, hN] at hh
    exact hh
  apply le_antisymm (centralizer_image_le s (c.Ugamma V₃))
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (s.mem_image D v).mp (hfixedD hv)
  refine (s.mem_image _ _).mpr ⟨u, ⟨u.property, ?_⟩, rfl⟩
  apply mem_centralizer_iff.mpr
  intro a ha
  let aH : H := ⟨a, hUgH ha⟩
  have haA : QuotientGroup.mk' (pCore 2 H) aH ∈ A := ⟨aH, ha, rfl⟩
  have hcZ : ⁅a, (u : G)⁆ ∈ V₁ := by
    apply (s.quotient_eq_zero_iff ⟨⁅a, (u : G)⁆, s.commutator_mem aH u⟩).mp
    rw [← s.displacement aH u]
    exact sub_eq_zero.mpr (hv ⟨_, haA⟩)
  have hn : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) := by
    apply le_trans ((conjugateSpanBy_mono d.seed_le le_rfl).trans hg.VH_endpoint)
    rw [c.vertexGroup_gamma, CriticalPair.Aone, ← map_equiv_normalizer_eq]
    exact map_mono (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hcA : ⁅a, (u : G)⁆ ∈ c.Aone V₁ := by
    have hc := commutator_commutatorPreimage_le (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁) hn
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator ha hu)
  have hz : ⁅a, (u : G)⁆ = 1 := by
    have hh : ⁅a, (u : G)⁆ ∈ V₁ ⊓ c.Aone V₁ := ⟨hcZ, hcA⟩
    rwa [hg.lines_disjoint, mem_bot] at hh
  exact commutatorElement_eq_one_iff_mul_comm.mp hz

/-- The original centralizer bound descends on the entire fixed space. -/
theorem source_fixedSpace_displacement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcmp : Reorientation.denominatorRank V₃ V₁ c ≤
      rank (Source.starImage H (c.Ugamma V₃)))
    (he : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) =
      2 * rank (Source.starImage H (c.Ugamma V₃))) :
    ∀ b ∈ Source.starImage H c.Vgamma,
      ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
        ρ b v - v ∈ s.image (c.Aone V₁) := by
  have hg := local_earlierGeometry d hF9 c
  let f := MulAut.conj (c.gb : G)
  have hC : Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G) ≤
      (Source.HC H V₃).map f.toMonoidHom := by
    intro x hx
    rw [mem_map_equiv]
    refine ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · have hh : x ∈ vertexGroup L (T : Subgroup G) H c.gamma :=
        hg.VH_endpoint ((conjugateSpanBy_mono d.seed_le le_rfl) hx.1)
      rw [c.vertexGroup_gamma, mem_map_equiv] at hh
      exact hh
    · intro y hy
      apply f.injective
      have hh := mem_centralizer_iff.mp hx.2 (f y) (mem_map_of_mem f.toMonoidHom hy)
      simpa only [map_mul, f.apply_symm_apply] using hh
  have hbase := Section07.centralizer_UH_commutator (localNaturalSetup d) hF9
  have hc := map_mono (f := f.toMonoidHom) hbase
  rw [map_commutator] at hc
  have hcomm : ⁅Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤
      c.Aone V₁ := (commutator_mono hC le_rfl).trans hc
  rw [← source_fixedSpace_eq_centralizer d hH hF9 c s hcmp he]
  exact s.displacement_mem _ _ _ (by rw [commutator_comm]; exact hcomm)

/-- Rank one and noncentrality on the two literal sections contradict the
original critical geometry, with no displacement or recognition callback. -/
theorem source_no_rank_one_configuration_from_geometry
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)
    (W : Subrepresentation ρ) (c : CriticalPair L (T : Subgroup G) H V)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hKQ : ∃ k ∈ Source.starImage H K,
      ∃ q : Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule, W.quotientRepresentation k q ≠ q)
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1)
    (hcmp : Reorientation.denominatorRank V₃ V₁ c ≤
      rank (Source.starImage H (c.Ugamma V₃)))
    (hVrank : 1 < rank (Source.starImage H c.Vgamma)) : False := by
  let s := FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.sourceSection
    H V₃ V₁ ρ hρ hF9.plus_le_H (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have hbound := (localNaturalSetup d).fixedCodim_le_twice_rank d.abelian_span hF9 s c hcmp
  have hg := local_earlierGeometry d hF9 c
  have hUgH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) := by
    refine ⟨?_, starImage_isElementaryAbelian H (c.Ugamma V₃) hUgH⟩
    intro hz
    rw [hz, Representation.BinaryOffender.rank_bot] at hrank
    omega
  have he := (source_rank_one_sections hH hKH hK hKn hKT e ρ W _
    hKW hKQ hA.1 hrank hbound).2.2.2.2.1
  apply source_no_rank_one_configuration_of_displacement d hH hKH hK hKn hKT e
    ρ W c hKW hKQ hA hrank hbound hVrank
  exact source_fixedSpace_displacement d hH hF9 c s hcmp (by rw [he, hrank])

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
