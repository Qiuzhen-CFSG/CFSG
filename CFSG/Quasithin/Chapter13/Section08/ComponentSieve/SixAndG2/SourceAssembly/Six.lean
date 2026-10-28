module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.G2
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Exports
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.GroupTheory.SylowNormalIntersectionIndex
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.FixedSpace

/-!
# The strict A₆ source branch and its literal parabolic

The fixed-space displacement theorem supplies the larger actor required by
13.8.23 when the selected actor has rank one. A normal-factor index
comparison reduces the actual L₁T parabolic to a proper Sylow overgroup
inside A₆. Its index-one alternative is impossible because the two-perfect
L₁ generates the nontrivial original seed. Thus the actual star parabolic
has Sylow index three, without assuming the ordinary local quotient.

These deductions supply all selected-pair, upper-action and parabolic
premises to the strict section-recognition theorem. Its conclusion retains
the original component quotient, both whole-module alternatives and the
L₁ chief factors. The preceding component and universal 13.7.6 inputs stay
explicit; the transvection branch and full 13.8.27 assembly remain with
`qt-d-138-six-g2-source`.

Source: Aschbacher–Smith, 13.8.23,26–27, printed pp.958,962–963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open CriticalGeometry SourceCompletion TransvectionRecognition.Component.ModelExtension
open AlternatingAndLinear.FourStructure.CriticalTransfer

private theorem codimension_two_of_no_rank_one
    {J E : Type*} [Group J] [Finite J] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) J E) (hf : Function.Injective ρ)
    (A : Subgroup J) (hA : IsElementaryTwo A) (hr : rank A = 1)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    fixedCodim ρ A = 2 * rank A := by
  have hc : Nat.card A = 2 := by simpa only [hr, pow_one] using hA.card_eq_two_pow_rank
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨g, hg⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hn : fixedCodim ρ A ≠ 1 := by
    rw [← hg, fixedCodim_zpowers_eq_displacement_rank]
    exact hno g
  have hp := fixedCodim_pos_of_faithful ρ hf hA.1
  omega

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The rank-one geometry required by the strict source recognition. -/
theorem six_larger_actor_of_selected_geometry
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcmp : Reorientation.denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hrank : 1 < rank (Source.starImage H c.Vgamma))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁) := by
  intro hr
  have hb := (localNaturalSetup d).fixedCodim_le_twice_rank d.abelian_span hF9 s c hcmp
  have hf := f9_section_faithful _ hF9 s
  have he := codimension_two_of_no_rank_one ρ hf _ hA hr hb hno
  refine ⟨Source.starImage H c.Vgamma, ?_,
    Seven.OriginalSource.source_fixedSpace_displacement d hHz hF9 c s hcmp he⟩
  apply lt_of_le_of_ne (map_mono (subgroupOf_mono H
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl))))
  intro hh
  change Source.starImage H (c.Ugamma V₃) = Source.starImage H c.Vgamma at hh
  rw [← hh, hr] at hrank
  omega


private theorem six_parabolic_indices
    {J : Type*} [Group J] [Finite J]
    (C : Subgroup J) [C.Normal] (e : C ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 J) (P : Subgroup J) (hSP : (S : Subgroup J) ≤ P)
    (hgen : C ⊔ (S : Subgroup J) = ⊤) (hproper : P ≠ ⊤) :
    (S : Subgroup J).relIndex P = 1 ∨ (S : Subgroup J).relIndex P = 3 := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal C
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let P' := (P.subgroupOf C).map e.toMonoidHom
  have hRP : (R' : Subgroup _) ≤ P' := by
    change (R : Subgroup C).map e.toMonoidHom ≤ (P.subgroupOf C).map e.toMonoidHom
    rw [hR]
    exact map_mono (subgroupOf_mono C hSP)
  have hP : P' ≠ ⊤ := by
    intro hh
    change (P.subgroupOf C).map e.toMonoidHom = ⊤ at hh
    have hPC : P.subgroupOf C = ⊤ := by
      apply (map_injective (f := e.toMonoidHom) e.injective)
      rw [hh, map_top_of_surjective _ e.surjective]
    have hCP : C ≤ P := by
      intro c hc
      have : (⟨c, hc⟩ : C) ∈ P.subgroupOf C := hPC ▸ mem_top _
      exact this
    exact hproper (top_unique (hgen ▸ sup_le hCP hSP))
  have hidx : (R' : Subgroup _).relIndex P' = (S : Subgroup J).relIndex P := by
    change ((R : Subgroup C).map e.toMonoidHom).relIndex
      ((P.subgroupOf C).map e.toMonoidHom) = (S : Subgroup J).relIndex P
    rw [relIndex_map_map_of_injective _ _ e.injective, hR]
    exact normal_intersection_relIndex _ _ C hSP (hgen ▸ le_top)
  have hcardR : Nat.card R' = 8 := by
    rw [Sylow.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel
  have hm := (R' : Subgroup _).subgroupOf P' |>.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv, hcardR] at hm
  change 8 * (R' : Subgroup _).relIndex P' = Nat.card P' at hm
  rw [hidx] at hm
  rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour R' P' hRP hP with hc | hc
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The source parabolic is not a two-group: its two-perfect residual moves
and generates the nontrivial original seed. -/
theorem source_parabolic_not_sylow
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ¬ sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ (T : Subgroup G) := by
  intro hp
  have hone : sourceOne L T V₁ ≤ (T : Subgroup G) := le_sup_left.trans hp
  have hperfect : IsPPerfect 2 (sourceOne L T V₁) := isPPerfect_embedded_pResidual 2 _
  have hid := hperfect.hom_eq_one_of_isPGroup (T.isPGroup'.to_le hone)
    (MonoidHom.id (sourceOne L T V₁))
  have hbot : sourceOne L T V₁ = ⊥ := by
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨x, hx⟩)
  have hdisp := (Section07.source_commutator_conclusions
    (localNaturalSetup d) hF9 hHz.2.1 hcomm).2.1
  have hseed := TransvectionRecognition.Solvable.seed_generation_of_core_displacement
    d hHz (local_flag_alternatives d)
    (fun W₁ W₃ a => CoverFactorization.source_factorization a) hdisp.symm
  rw [hbot, commutator_bot_right] at hseed
  have hc := d.seed_card
  rw [hseed, card_bot] at hc
  contradiction

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- In the A₆ component branch the literal star parabolic has Sylow index
three. The index-one option would collapse the two-perfect seed mover. -/
theorem six_source_parabolic_index
    {K : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hgen : H = K ⊔ (T : Subgroup G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    (Source.starImage H (T : Subgroup G)).relIndex
      (Source.starImage H (sourceOne L T V₁ ⊔ (T : Subgroup G))) = 3 := by
  let B := sourceOne L T V₁ ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hHz.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hBH
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup _) = Source.starImage H (T : Subgroup G) := rfl
  let : (Source.starImage H K).Normal := Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hstar : Source.starImage H K ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS, Source.starImage, Source.starImage, ← Subgroup.map_sup, ← subgroupOf_sup hKH hTH,
      ← hgen, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hk : pCore 2 H ≤ (T : Subgroup G).subgroupOf H := by
    intro x hx
    exact hF9.QH_le_T (mem_map_of_mem H.subtype hx)
  have hproper : Source.starImage H B ≠ ⊤ := by
    intro hh
    have he : B.subgroupOf H = ⊤ := by
      have hfull := congrArg (comap (QuotientGroup.mk' (pCore 2 H))) hh
      rw [Source.starImage, comap_map_eq, comap_top, QuotientGroup.ker_mk',
        sup_eq_left.mpr (hk.trans (subgroupOf_mono H le_sup_right))] at hfull
      exact hfull
    have hHB : H ≤ B := by
      intro x hx
      exact (show (⟨x, hx⟩ : H) ∈ B.subgroupOf H from he ▸ mem_top _)
    have hBM : B ≤ M := by
      change one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤ M
      rw [← Comparison.local_edge d hF9]
      have hLM : L ⊔ (T : Subgroup G) ≤ M := by
        rw [d.local_normalizer]
        exact sup_le L.le_normalizer d.normalizes_L
      exact inf_le_left.trans hLM
    exact hHz.2.2 (hHB.trans hBM)
  have hidx : (Source.starImage H (T : Subgroup G)).relIndex (Source.starImage H B) =
      (T : Subgroup G).relIndex B := by
    rw [Source.starImage, Source.starImage, relIndex_map_map, QuotientGroup.ker_mk',
      sup_eq_left.mpr hk, sup_eq_left.mpr (hk.trans (subgroupOf_mono H le_sup_right)),
      relIndex_subgroupOf hBH]
  rcases six_parabolic_indices (Source.starImage H K)
    ((Components.componentStarEquiv H K hKH hK).symm.trans eK) S (Source.starImage H B)
    (by rw [hS]; exact map_mono (subgroupOf_mono H le_sup_right)) hstar hproper with hh | hh
  · rw [hS, hidx] at hh
    exact (source_parabolic_not_sylow d hHz hF9 hcomm (relIndex_eq_one.mp hh)).elim
  · exact hh


open FieldComponents.HigherFieldReduction.ExternalModules
open TransvectionRecognition TransvectionRecognition.Component
open scoped Pointwise

/-- The strict A₆ branch constructs every selected-pair premise of section
recognition, including the larger actor and the index-three parabolic. -/
theorem six_alternative_of_no_rank_one
    {K : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hgen : H = K ⊔ (T : Subgroup G))
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    ∃ eK' : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK' ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      SourceSix.MarkedFullAction hKH eK' ρ ∧
      Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hHz.1.2) ρ) := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  have hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · rw [hgen]
      exact sup_le_sup le_rfl le_sup_right
    · exact sup_le hKH hHz.1.2
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  have hqs := (SixRecognition.Constituents.component_properties _ hfit.symm e).1
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hHz hF9 hjoin hK hN hqs
    hcentral hcomm ρ hρ hno
  let c := w.pair
  have geo := local_earlierGeometry d hF9 c
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have hf := f9_section_faithful _ hF9 s
  have inputs := CriticalSource.earlier_inputs d hHz hF9 hcentral hcomm ρ hρ
  have hUg : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans geo.Vgamma_H
  have hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [← c.vertexGroup_gamma]
    exact (conjugateSpanBy_mono d.seed_le le_rfl).trans geo.VH_endpoint
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) :=
    ⟨by intro he; have := w.positive; rw [he, Representation.BinaryOffender.rank_bot] at this; omega,
      starImage_isElementaryAbelian H _ hUg⟩
  have hcrit := Nat.log_mono_right (b := 2)
    (c.index_comparison_of_selected_rank V₃ V₁ hUg geo.Dgamma_kernel w.comparison)
  obtain ⟨a, _⟩ := Terminal.exists_rank_section_action d hF9 hHz.2.1 hcomm
  let t : PairConsequences.UpperSection H (Source.VH H V) (Source.UH H V₃)
      (SolvableExclusion.Three.Supercritical.Offenders.linearAction a) := {
    le := conjugateSpanBy_le_self hF9.V_le_H
    normalizes := a.normalizes
    kernel_le := conjugateSpanBy_mono d.seed_le le_rfl
    quotient := (MulEquiv.multiplicativeAdditive (Source.Vsection H V V₃)).symm.toMonoidHom.comp
      (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)))
    surjective := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel := by ext x; exact QuotientGroup.eq_one_iff x
    conjugates := fun h v => congrArg Additive.ofMul (a.conjugation h v) }
  have hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃ := by
    have hh := (quadratic_of_normalizes_abelian (Source.VH H V) (c.Ugamma V₃)
      (geo.VH_endpoint.trans (c.normalizes_Ugamma V₃)) inferInstance)
    rw [commutator_comm (Source.VH H V), commutator_comm _ (c.Ugamma V₃)] at hh
    exact hh.le.trans bot_le
  let S := (T.subtype (le_sup_right.trans hHz.1.2)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup _) = Source.starImage H (T : Subgroup G) := rfl
  have hi := six_source_parabolic_index d hHz hF9 hcomm hKH hK hN hgen eK
  have hnorm : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) := by
    change one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤ _
    rw [← Comparison.local_edge d hF9]
    exact inf_le_left.trans d.normalizes_V
  exact SixRecognition.Constituents.source_alternative_strict T d earlier hHz c ρ s hf
    geo.Vgamma_H hreverse d.line_card hcrit
    (SolvableExclusion.Three.Supercritical.Offenders.linearAction a) t hquad hA
    (inputs.estimate c w.positive w.comparison)
    (six_larger_actor_of_selected_geometry d hHz hF9 c ρ s w.comparison w.rank_gt_one hA hno)
    hKH hK eK hfit.symm hρ hUK (sourceOne L T V₁) (le_sup_left.trans hHz.1.2)
    (le_sup_right.trans hHz.1.2) S hS hi d.seed_le (Comparison.local_seed_index d)
    hnorm inputs.noncentral w.conjugator w.conjugate_le_core

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
