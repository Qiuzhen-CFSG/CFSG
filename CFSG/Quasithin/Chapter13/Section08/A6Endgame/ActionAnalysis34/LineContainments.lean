module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.Symmetry
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.CommonAxis
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.Sections
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.EndpointSource
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.EndpointActor

/-!
# The local geometry of the line-containment argument

Starting in the orientation A₁≰U_H, transport of 13.7.3(7) makes D_H
centralize Vγ. The faithful action on the literal U_H/V₁ then gives
Vγ*=Uγ* of rank one. Equality of the actual star images supplies the
commutator comparison; endpoint generation, as in 13.8.9, proves
V₁≰Uγ and the transvection center on Vγ/Uγ. Corrected 13.8.10 gives
the transvection axis on Uγ and the opposite axis on U_H.

The original compatible section actions construct both endpoint actions.
Their common nonidentity involution has displacement at most one on each.
Transport of the original plane marking gives the actual noncentral syntheme
quotient. In the symmetric case the natural/augmentation comparison preserves
the actor, forcing displacement at least two on that quotient; alternating
faithfulness excludes the same actor directly. Thus the oriented failure is
impossible.

`line_containments_of_star_rank_one` completes the conditional deduction of
both lines. The genuine reversal exchanges the indices, line conditions and
F.9 placements; terminal-edge conjugation transports the original edge action.
All earlier source inputs are displayed, including the F.9 kernel identity,
the original marked models, and the 13.8.9 generation premise at the two
orientations. The rank-one conclusion itself and the discharge of these earlier
inputs remain with the owner of the full Lemma 13.8.34.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 13.8.9–10 and 13.8.34(1), printed pp.949–950,968.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
open CriticalGeometry CriticalGeometry.SectionActions
variable {G : Type*} [Group G] [Finite G]

/-- The oriented geometry produces the two actual endpoint actions, using
relative generation and the source kernel identity. Neither transvection
action nor the failure V₁≰Uγ is an input. -/
theorem oriented_section_actions
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)] [IsElementaryAbelian 2 c.Vgamma]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hZU : Z ≤ Source.UH H V₃)
    (hZ : Nat.card Z = 2) (hz : H ≤ normalizer (Z : Set G))
    (hVγH : c.Vgamma ≤ H) (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hbaseKernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) Z)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hkernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hγindex : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃) = 2)
    (hHindex : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex
      (Source.UH H V₃) = 2)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hact : ∀ h : H, ρ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (model : Nonempty (Source.Hstar H ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)))
    (hnot : ¬ c.Aone Z ≤ Source.UH H V₃) :
    Source.starImage H c.Vgamma = Source.starImage H (c.Ugamma V₃) ∧
    Representation.BinaryOffender.rank (Source.starImage H c.Vgamma) = 1 ∧
    HasTransvectionCenter (Source.UH H V₃) c.Vgamma (c.Ugamma V₃) Z
      (hUJ.trans (c.normalizes_Ugamma V)) (hUJ.trans (c.normalizes_Ugamma V₃)) ∧
    HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z)
      (hUJ.trans (c.normalizes_Ugamma V₃)) ∧
    HasTransvectionAxis (c.Ugamma V₃) (Source.UH H V₃)
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z))
      (((map_mono (conjugateSpanBy_mono hV₃V le_rfl)).trans hVγH).trans
        (le_normalizer_conjugateSpanBy V₃ H)) := by
  have hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ Z := by
    rw [commutator_comm, hbaseKernel]
    exact commutator_commutatorPreimage_le H (Source.UH H V₃) Z hz
  have hρ := faithful_of_conjugation_kernel H (Source.UH H V₃) Z
    (le_normalizer_conjugateSpanBy V₃ H) hz hbaseKernel ρ hact
  have hUHH : Source.UH H V₃ ≤ H := conjugateSpanBy_le_self (hV₃V.trans hVH)
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃V le_rfl)
  have hUγH := hUV.trans hVγH
  have hcentral := (denominator_centralizes_endpoint c V₃ Z hV₃V hZ hnot hz hUJ hVγH hHC).2
  have hc : Nat.card (Source.starImage H (c.Ugamma V₃)) = 2 := by
    rw [starImage_card H (c.Ugamma V₃) hUγH, ← inf_relIndex_left, ← hkernel]
    exact hγindex
  have hi := star_eq_of_centralized_index_two H (Source.UH H V₃) Z (c.Ugamma V₃)
    c.Vgamma (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z))
    (le_normalizer_conjugateSpanBy V₃ H) hz hVγH hUV ρ hρ hact model hc hHindex
    (by rwa [commutator_comm])
  have hb := commutator_bound_of_equal_starImage H (Source.UH H V₃) (c.Ugamma V₃)
    c.Vgamma Z hUHH hVγH (hZU.trans hUHH) hz hUV
    (hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)) hQ hi.1.symm
  have hn := c.noncentral_of_generation V₃ (Source.UH H V₃) hVH hUJ hgen hedge hnoncentral
  have hcenter := center_of_bound (vertexGroup L T H c.gamma) (Source.UH H V₃)
    c.Vgamma (c.Ugamma V₃) Z hUJ
    (by rw [c.vertexGroup_gamma]; exact map_mono (conjugateSpanBy_le_self hVH))
    (hZU.trans hUJ) hUV (c.normalizes_Ugamma V) (c.normalizes_Ugamma V₃) hZ hb hn
  have hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    rw [he, relIndex_self] at hHindex
    omega
  have haxis := (corrected_rank_one (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) Z
    hproper (by omega) hγindex hZ (hUJ.trans (c.normalizes_Ugamma V₃))
    (hUγH.trans hz)).2.resolve_left hcenter.2.1
  refine ⟨hi.1, hi.2, hcenter, haxis, ?_⟩
  apply axis_of_noncontained_line (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) Z
    (hUγH.trans (le_normalizer_conjugateSpanBy V₃ H))
    (hUJ.trans (SectionActions.CriticalPair.normalizes_Aone c Z hz)) hγindex hHindex _ hnot
  change Nat.card (Z.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
  rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective, hZ]

variable {L T H V : Subgroup G}

/-- Construct the compatible endpoint representations from the two original
source actions using inverse conjugation by the specified `c.gb`. This works
at each genuine critical pair, including the constructed reversal. -/
noncomputable def endpointActionsOfSource
    (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)] [IsElementaryAbelian 2 c.Vgamma]
    (hz : H ≤ normalizer (Z : Set G))
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hτ : ∀ h : H, τ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ) : EndpointActions c V₃ Z hz where
  onU := ((SectionActions.CriticalPair.uLinearEquiv c V₃ Z).symm.conjRingEquiv.toMonoidHom).comp
    (τ.comp (EndpointSource.starEquiv c).toMonoidHom)
  onV := ((SectionActions.CriticalPair.vLinearEquiv c V₃).symm.conjRingEquiv.toMonoidHom).comp
    (σ.comp (EndpointSource.starEquiv c).toMonoidHom)
  onU_mk j := by
    ext w
    apply (SectionActions.CriticalPair.uLinearEquiv c V₃ Z).injective
    change (SectionActions.CriticalPair.uLinearEquiv c V₃ Z)
      ((SectionActions.CriticalPair.uLinearEquiv c V₃ Z).symm
        (τ (EndpointSource.starEquiv c (QuotientGroup.mk' _ j))
          (SectionActions.CriticalPair.uLinearEquiv c V₃ Z w))) = _
    rw [LinearEquiv.apply_symm_apply, EndpointSource.starEquiv_mk, hτ]
    exact (SectionActions.CriticalPair.uSectionEquiv_intertwines c V₃ Z
      (vertexGroup L T H c.gamma) hz le_rfl j w.toMul).symm
  onV_mk j := by
    ext w
    apply (SectionActions.CriticalPair.vLinearEquiv c V₃).injective
    change (SectionActions.CriticalPair.vLinearEquiv c V₃)
      ((SectionActions.CriticalPair.vLinearEquiv c V₃).symm
        (σ (EndpointSource.starEquiv c (QuotientGroup.mk' _ j))
          (SectionActions.CriticalPair.vLinearEquiv c V₃ w))) = _
    rw [LinearEquiv.apply_symm_apply, EndpointSource.starEquiv_mk]
    have hi := SectionActions.CriticalPair.vSectionEquiv_intertwines c V₃
      (vertexGroup L T H c.gamma) le_rfl j w.toMul
    refine Eq.trans ?_ hi.symm
    change σ (QuotientGroup.mk' (pCore 2 H) (EndpointSource.actorEquiv c j))
      (Additive.ofMul (SectionActions.CriticalPair.vSectionEquiv c V₃ w.toMul)) =
      Additive.ofMul (vAction H V V₃ (EndpointSource.actorEquiv c j)
        (SectionActions.CriticalPair.vSectionEquiv c V₃ w.toMul))
    generalize SectionActions.CriticalPair.vSectionEquiv c V₃ w.toMul = x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
      ((Source.UH H V₃).subgroupOf (Source.VH H V)) x
    exact (hσ (EndpointSource.actorEquiv c j) v).trans
      (congrArg Additive.ofMul (quotientAction_apply H (Source.VH H V) (Source.UH H V₃) _ _
        (EndpointSource.actorEquiv c j) v)).symm

omit [Finite G] in
private theorem endpoint_kernel
    (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    (hz : H ≤ normalizer (Z : Set G)) (hγH : c.Ugamma V₃ ≤ H)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) Z) :
    Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z = c.Ugamma V₃ ⊓ Source.QH H := by
  rw [hk]
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    exact le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hγH)
      (commutator_commutatorPreimage_le _ _ _ (hγH.trans hz))
  · exact le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ hz))

open ComponentSieve.SixAndG2.NaturalSix

/-- The original plane marking, together with the natural or augmentation
comparison in the symmetric case. These are source module identifications. -/
@[expose] def MarkedSourceModels (H M V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z))) : Prop :=
  (∃ e : Source.Hstar H ≃* alternatingGroup (Fin 6),
    (Source.starImage H (H ⊓ M)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer) ∨
  (∃ e : Source.Hstar H ≃* Symmetric,
    (Source.starImage H (H ⊓ M)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2 ∧
    ((∃ q : Additive (Source.Utilde H V₃ Z) ≃ₗ[ZMod 2] Natural,
        ∀ a v, q (τ a v) = symmetricAction (e a) (q v)) ∨
      (∃ q : Additive (Source.Utilde H V₃ Z) ≃ₗ[ZMod 2] Augmentation,
        ∀ a v, q (τ a v) = BinaryPermutation.coreRepresentation (Fin 6) (e a) (q v))))

/-- The oriented line follows from the earlier geometric inputs and the
original marked modules. The common endpoint actor and its two displacement
bounds are derived, and both source model branches are discharged. -/
theorem aone_le_of_indices
    (c : CriticalPair L T H V) (M V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃V : V₃ ≤ V) (hflag : V₃.relIndex V = 2) (hVH : V ≤ H)
    (hZU : Z ≤ Source.UH H V₃) (hZ : Nat.card Z = 2)
    (hz : H ≤ normalizer (Z : Set G))
    (hVγH : c.Vgamma ≤ H) (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hbaseKernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) Z)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hγindex : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃) = 2)
    (hHindex : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex
      (Source.UH H V₃) = 2)
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hτ : ∀ h : H, τ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ)
    (models : MarkedSourceModels H M V₃ Z τ) :
    c.Aone Z ≤ Source.UH H V₃ := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := EndpointSource.elementary_Ugamma c V₃
  let _ : IsElementaryAbelian 2 c.Vgamma := EndpointSource.elementary_Vgamma c
  by_contra hnot
  have hmodel : Nonempty (Source.Hstar H ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)) := by
    rcases models with ⟨e, _⟩ | ⟨e, _⟩
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  have hk := endpoint_kernel c V₃ Z hz
    ((map_mono (conjugateSpanBy_mono hV₃V le_rfl)).trans hVγH) hbaseKernel
  obtain ⟨_, _, hcenter, haxis, _⟩ := oriented_section_actions c V₃ Z
    hV₃V hVH hZU hZ hz hVγH hUJ hHC hbaseKernel hnoncentral hgen hedge
    hk hγindex hHindex τ hτ hmodel hnot
  let E := endpointActionsOfSource c V₃ Z hz τ hτ σ hσ
  obtain ⟨t, ht, ht2, htU, htV, _⟩ := exists_common_endpoint_actor c V₃ Z hz hUJ E hcenter haxis
  rcases models with ⟨e, hmark⟩ | ⟨e, hmark, hmodule⟩
  · obtain ⟨f, hf, he, hnc, _⟩ := EndpointSource.alternating_source c Z hz E M e
      hmark hV₃V hflag hnoncentral hnorm
    exact LineObstruction.alternating_quotient_not_small (EndpointSource.marking c e)
      E.onV f hf he hnc t ht htV
  · obtain ⟨f, hf, he, hnc, _⟩ := EndpointSource.symmetric_source c Z hz E M e
      hmark hV₃V hflag hnoncentral hnorm
    have hm := EndpointSource.symmetric_natural_or_cover c Z hz E e τ hτ hmodule
    have hge := LineObstruction.symmetric_natural_or_cover_rank_ge_two
      (EndpointSource.marking c e) E.onU hm E.onV f hf he hnc t ht ht2 htU
    omega

open CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData

omit [Finite G] in
/-- The two F.9 placements exchange through the actual reversal transporter.
The endpoint stabilizer adjustment fixes H and its conjugate span. -/
theorem reversal_placements (c : CriticalPair L T H V) (r : Reversal c)
    (hVγH : c.Vgamma ≤ H) (hVHJ : Source.VH H V ≤ vertexGroup L T H c.gamma) :
    r.pair.Vgamma ≤ H ∧ Source.VH H V ≤ vertexGroup L T H r.pair.gamma := by
  have hVH := le_normalizer_conjugateSpanBy V H
  have hVret := return_map r (Source.VH H V) hVH
  have hVend := endpoint_map r (Source.VH H V) hVH
  have hHret := return_map r H H.le_normalizer
  have hHend := endpoint_map r H H.le_normalizer
  change c.Vgamma.map _ = Source.VH H V at hVret
  change r.pair.Vgamma = _ at hVend
  rw [← c.vertexGroup_gamma] at hHret
  rw [← r.pair.vertexGroup_gamma] at hHend
  constructor
  · exact hVend.le.trans ((map_mono hVHJ).trans hHret.le)
  · exact hVret.ge.trans ((map_mono hVγH).trans hHend.ge)

omit [Finite G] in
private theorem endpoint_edge_action (d : CriticalPair L T H V) (V₃ : Subgroup G)
    (hedge : ⁅(L ⊔ T) ⊓ H, V⁆ ≤ Source.UH H V₃) :
    ⁅edgeGroup L T H d.gamma d.previous,
      V.map (MulAut.conj (d.gb : G)).toMonoidHom⁆ ≤ d.Ugamma V₃ := by
  have hp : vertexGroup L T H d.previous =
      (L ⊔ T).map (MulAut.conj (d.gb : G)).toMonoidHom := by
    change vertexGroup L T H (d.path.getVert (d.path.length - 1)) = _
    rw [← d.gb_zero, vertexGroup_smul, vertexGroup_base]
    rfl
  have he : edgeGroup L T H d.gamma d.previous =
      ((L ⊔ T) ⊓ H).map (MulAut.conj (d.gb : G)).toMonoidHom := by
    rw [edgeGroup, d.vertexGroup_gamma, hp,
      ← map_inf _ _ _ (MulAut.conj (d.gb : G)).injective, inf_comm H]
  rw [he, ← map_commutator]
  exact map_mono hedge

/-- Conditional local-geometric deduction of 13.8.34(1) from (2).
The earlier generation assertion `hgen` is required at the original pair
and its genuine reversals, exactly in the form used by 13.8.9. All subgroup
placements, edge actions, section actions and model markings are transported
from the original data. The kernel identity derives each oriented kernel;
the rank comparison is required only at the original pair. Reversal exchanges
the resulting indices and the two line conditions through its transporter. -/
theorem line_containments_of_star_rank_one
    (c : CriticalPair L T H V) (M V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃V : V₃ ≤ V) (hflag : V₃.relIndex V = 2) (hVH : V ≤ H)
    (hZU : Z ≤ Source.UH H V₃) (hZ : Nat.card Z = 2)
    (hz : H ≤ normalizer (Z : Set G))
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hbaseKernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) Z)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (hb : 3 ≤ c.path.length)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hVγH : c.Vgamma ≤ H)
    (hVHJ : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hedge : ⁅(L ⊔ T) ⊓ H, V⁆ ≤ Source.UH H V₃)
    (hgen : ∀ d : CriticalPair L T H V,
      (d = c ∨ ∃ r : Reversal c, d = r.pair) →
      Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ →
      vertexGroup L T H d.gamma =
        conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃)
    (hcomparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃))
    (hrank : Representation.BinaryOffender.rank (Source.starImage H (c.Ugamma V₃)) = 1)
    (τ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ Z)))
    (hτ : ∀ h : H, τ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap)
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ)
    (models : MarkedSourceModels H M V₃ Z τ) :
    c.Aone Z ≤ Source.UH H V₃ ∧ Z ≤ c.Ugamma V₃ := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := EndpointSource.elementary_Ugamma c V₃
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hV₃V le_rfl
  have hUJ := hUV.trans hVHJ
  have hUγH := (map_mono (conjugateSpanBy_mono hV₃V le_rfl)).trans hVγH
  have hk := endpoint_kernel c V₃ Z hz hUγH hbaseKernel
  obtain ⟨hγindex, hHindex⟩ := indices_of_star_rank_one H (Source.UH H V₃)
    (c.Ugamma V₃) (c.Aone Z) Z hUγH hrank hk hproper hcomparison
  have hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    rw [he, relIndex_self] at hγindex
    omega
  by_contra hfail
  obtain ⟨d, hd, hnot, hdγ, hdH⟩ := exists_oriented_failure c V₃ Z hz hb hV₃V hVγH
    hF915 (hUJ.trans (SectionActions.CriticalPair.normalizes_Aone c Z hz))
    hstrict hγindex hHindex hfail
  have hplacement : d.Vgamma ≤ H ∧ Source.VH H V ≤ vertexGroup L T H d.gamma := by
    rcases hd with rfl | ⟨r, rfl⟩
    · exact ⟨hVγH, hVHJ⟩
    · exact reversal_placements c r hVγH hVHJ
  have hdproper : Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    rw [he, relIndex_self] at hdH
    omega
  exact hnot (aone_le_of_indices d M V₃ Z hV₃V hflag hVH hZU hZ hz hplacement.1 (hUV.trans hplacement.2)
    hHC hbaseKernel hnoncentral hnorm (hgen d hd hdproper)
    (endpoint_edge_action d V₃ hedge) hdγ hdH τ hτ σ hσ models)

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
