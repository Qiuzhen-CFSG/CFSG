module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.AlternatingBounds
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ContainedAlternating
/-!
# The original seven-letter point in whole-module coordinates

The component section and the full module both have the six-dimensional
natural model. Their actual quotient map is therefore injective. Composing
its inverse comparison with the original section marking retains the exact
point of V₂. The component normalizer then extends these coordinates to H*.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open PointRanks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

private theorem seven_marking_lifts
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Section08.Source.UH H V₃ = ⁅Section08.Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (u : commutatorImage H V₃ V₁ K)
    (hpair : HasSevenPairPoint H V₃ V₁ K ρ hKH eK u) :
    ∃ eU : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 7),
      (∀ a v, eU (ρ (modelActor hKH hK eK a) v) =
        alternatingNaturalRepresentation (Fin 7) a (eU v)) ∧
      BinaryPermutation.PointStabilizerRank.IsPairVector (eU u) := by
  obtain ⟨hs,e,he,hp⟩ := hpair
  obtain ⟨e₀, _⟩ := alternatingSeven_module_of_section hKH hK ρ hρ hgen eK ⟨hs,e,he⟩
  let S := commutatorImage H V₃ V₁ K
  let F := fixedInCommutator H V₃ V₁ ρ K
  let j : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] S :=
    (LinearEquiv.ofTop S (commutatorImage_eq_top hgen)).symm
  let p := e.toLinearMap.comp (F.mkQ.comp j.toLinearMap)
  have hj (v) : (j v).val = v := LinearEquiv.coe_ofTop_symm_apply _ _
  have hj' : j u.val = u := Subtype.ext (hj u.val)
  have hps : Function.Surjective p :=
    e.surjective.comp ((Submodule.mkQ_surjective F).comp j.surjective)
  let : Module.Finite (ZMod 2) (Additive (Section08.Source.Utilde H V₃ V₁)) :=
    Module.Finite.of_finite
  have hpi : Function.Injective p :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e₀.finrank_eq).mpr hps
  let eU := LinearEquiv.ofBijective p ⟨hpi,hps⟩
  refine ⟨eU, ?_, ?_⟩
  · intro a v
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (eK.symm a)
    have hka : eK (QuotientGroup.mk' (pCore 2 K) k) = a := by rw [hk]; simp
    rw [← hka, modelActor_mk]
    change e (Submodule.Quotient.mk (j (ρ _ v))) =
      alternatingNaturalRepresentation (Fin 7) _ (e (Submodule.Quotient.mk (j v)))
    convert he k (j v) using 2
    congr 2
  · change BinaryPermutation.PointStabilizerRank.IsPairVector (e (Submodule.Quotient.mk (j u.val)))
    rw [hj']
    exact hp

include d
/-- The original pair point and full H* action in one compatible coordinate system. -/
theorem seven_marked_full_action_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentral : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 7)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    ∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 7))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 7))
      (v : V₂) (i j : Fin 7),
      Function.Injective f ∧
      (∀ k : Section08.Source.starImage H K, f k = (componentModelEquiv hKH hK eK k).val) ∧
      (∀ a w, eV (ρ a w) = coreRepresentation (Fin 7) (f a) (eV w)) ∧
      i ≠ j ∧
      (eV (seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩)).val =
        Pi.single i 1 + Pi.single j 1 := by
  have hprod := (contained_seven_full_action d hH hF9 hKH hK hL₁K ρ hρ eK hs).1
  obtain ⟨hKn, hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  have hNi := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : (Section08.Source.starImage H K).Normal :=
    Subgroup.Normal.map hNi (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨v, _, hp⟩ := seven_plane_pair_of_one_le d hH hKH hL₁K ρ hρ hcentral eK hs
  obtain ⟨eU, heU, i, j, hij, hv⟩ := seven_marking_lifts hKH hK ρ hρ hgen.symm eK _ hp
  let c := coreEquivNatural (Fin 7) (by decide : Odd (Fintype.card (Fin 7)))
  let eV := eU.trans c.symm
  have heV : ∀ k : Section08.Source.starImage H K, ∀ w,
      eV (ρ k w) = alternatingCoreRepresentation (Fin 7)
        (componentModelEquiv hKH hK eK k) (eV w) := by
    intro k w
    apply c.injective
    change c (c.symm (eU (ρ k w))) =
      c (coreRepresentation (Fin 7) (componentModelEquiv hKH hK eK k).val (c.symm (eU w)))
    rw [c.apply_symm_apply, coreEquivNatural_equivariant, c.apply_symm_apply]
    simpa only [modelActor_componentModelEquiv, alternatingNaturalRepresentation,
      MonoidHom.comp_apply, Subgroup.coe_subtype] using heU (componentModelEquiv hKH hK eK k) w
  have hfρ : Function.Injective ρ := by
    apply faithful_of_centralizer_le_core ρ hρ
    intro x hx
    change x ∈ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH
    rw [← hF9.kernel_UH_eq_QH]
    apply (hF9.mem_kernel_iff hF9.UH_le_H).mpr
    refine ⟨commutatorPreimage_le _ _ _ hx, ?_⟩
    intro u hu
    rw [← commutatorElement_inv]
    apply V₁.inv_mem
    exact commutator_commutatorPreimage_le H (Section08.Source.UH H V₃) V₁
      (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
        (commutator_mem_commutator hx hu)
  obtain ⟨f, hf, hfK, hfV⟩ := SevenExtension.faithful_extension
    (Section08.Source.starImage H K) ρ hfρ (componentModelEquiv hKH hK eK) eV heV
  exact ⟨hprod, f, eV, v, i, j, hf, hfK, hfV, hij, hv⟩

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
