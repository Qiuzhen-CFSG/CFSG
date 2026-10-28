module

public import Theory.Representation.SixLetterTransvections
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.MarkedQuotient
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineObstruction
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.SourceResidual
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments
import Mathlib.Tactic

/-!
# Rank and line analysis for the marked A₆ endgame

This module assembles the rank and line deductions of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March
2004), Lemma 13.8.34, printed p.968 (PDF p.985).

The faithful-action obstruction is proved for every binary A₆/S₆ module
in `SixLetterTransvections`. The source dimension balance then rules out
rank at least two once the marked natural-module calculation bounds the
codimension of Uγ∩UH. The quotient subspace is the actual D/I, retaining
the intersection that occurs in the source's displayed equation.

Separately, the marked noncontainment makes Vα* a proper subgroup of
R₁*, whose order is at most eight. Its conjugate Vγ* therefore has rank
at most two and, when elementary abelian, order at most four. Both the
star map H → H/O₂(H) and the γ-to-α conjugator are explicit; the two-core
is relative to L₁*, not normality in the ambient simple group.

The literal source permutation quotient is now transported to the named
syntheme coordinates, with noncentrality and faithfulness derived. The
quadratic obstruction excludes the relative two-core under its explicit
marking. In the alternating case the radical bound already gives rank one.
The natural/cover transvection contradiction is proved using the same actor
marking on the syntheme quotient; the identity actor is explicitly excluded.

`lemma_13_8_34` proves every source conclusion from the explicit earlier
local inputs. The actual residual image determines the core marking. The
case-two placement in O₂(H∩M) supplies the radical bound; the marked
natural/cover displacement lifts through the actual commutator to the
intersection estimate. The critical-pair reversal then proves both lines.
The section assembly owner retains the earlier local inputs, including the
case-two selection after 13.8.33 and the compatible marked module models.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame
open Subgroup Representation.BinaryOffender

variable {G : Type*} [Group G] [Finite G]

/-- The rank consequence of the marked noncontainment, with the conjugator
from γ to α specified in the actual quotient H/O₂(H). -/
theorem star_rank_le_two_of_marked_noncontainment
    (H L₁ Vα Vγ : Subgroup G) (R : Subgroup (Source.Hstar H))
    (c : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj c).toMonoidHom =
      Source.starImage H Vα)
    (hVR : Source.starImage H Vα ≤ R)
    (hcoreR : (Source.starImage H L₁).pCoreIn 2 ≤ R)
    (hR : Nat.card R ≤ 8)
    (hnot : ¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα) :
    rank (Source.starImage H Vγ) ≤ 2 := by
  have hlt : Nat.card (Source.starImage H Vα) < Nat.card R := by
    by_contra hn
    have he := Subgroup.eq_of_le_of_card_ge hVR (Nat.le_of_not_gt hn)
    exact hnot (hcoreR.trans he.ge)
  have hsmall : Nat.card (Source.starImage H Vα) ≤ 7 := by omega
  have hlog := Nat.log_monotone (b := 2) hsmall
  have hcard : Nat.card (Source.starImage H Vα) = Nat.card (Source.starImage H Vγ) := by
    rw [← hconj]
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [hcard] at hlog
  exact hlog

/-- The order form required by the terminal comparison, for the actual
nontrivial elementary abelian image Vγ*. -/
theorem star_card_le_four_of_marked_noncontainment
    (H L₁ Vα Vγ : Subgroup G) (R : Subgroup (Source.Hstar H))
    (c : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj c).toMonoidHom =
      Source.starImage H Vα)
    (hVR : Source.starImage H Vα ≤ R)
    (hcoreR : (Source.starImage H L₁).pCoreIn 2 ≤ R)
    (hR : Nat.card R ≤ 8)
    (hnot : ¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα)
    (hVγ : IsElementaryTwo (Source.starImage H Vγ)) :
    Nat.card (Source.starImage H Vγ) ≤ 4 := by
  rw [hVγ.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (star_rank_le_two_of_marked_noncontainment H L₁ Vα Vγ R c hconj hVR hcoreR hR hnot)

variable {W U : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [Module.Finite (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
  [Module.Finite (ZMod 2) U]

/-- The dimension calculation in the second paragraph of 13.8.34. In the
source U is a coordinate space for Uγ, D for Dγ, and I for Uγ∩UH. The
codimension bound must come from the marked natural-module calculation.
The displacement bound is on the faithful action on VH/UH. -/
theorem star_rank_one_of_dimension_balance
    (H Uγ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) W) (hρ : Function.Injective ρ)
    (model : Nonempty (Source.Hstar H ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)))
    (hUγ : IsElementaryTwo (Source.starImage H Uγ))
    (D I : Submodule (ZMod 2) U) (hID : I ≤ D)
    (hbalance : Module.finrank (ZMod 2) D + rank (Source.starImage H Uγ) =
      Module.finrank (ZMod 2) U)
    (hcodim : 1 < rank (Source.starImage H Uγ) →
      Module.finrank (ZMod 2) (U ⧸ I) ≤ 3)
    (hcomm : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (Source.starImage H Uγ)) ≤
      Module.finrank (ZMod 2) (D ⧸ I.comap D.subtype)) :
    rank (Source.starImage H Uγ) = 1 := by
  have hpos := hUγ.rank_pos
  by_contra hn
  have hlarge : 1 < rank (Source.starImage H Uγ) := by omega
  have hI := I.finrank_quotient_add_finrank
  have hD := (I.comap D.subtype).finrank_quotient_add_finrank
  have he := (Submodule.comapSubtypeEquivOfLe hID).finrank_eq
  have hc := hcodim hlarge
  have hline : Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ (Source.starImage H Uγ)) ≤ 1 := by omega
  have hr := Representation.SixLetterTransvections.rank_le_one_of_common_displacement
    ρ hρ model (Source.starImage H Uγ) hline
  omega

open Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-- The symmetric dimension-balance argument with faithfulness proved from
the noncentral marked quotient, rather than supplied as another source premise. -/
theorem symmetric_star_rank_one_of_dimension_balance
    (H Uγ : Subgroup G) (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (f : P →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rho (e g) v) = ρ g (f v))
    (hnc : ∃ g v, ρ g v ≠ v)
    (hUγ : IsElementaryTwo (Source.starImage H Uγ))
    (D I : Submodule (ZMod 2) U) (hID : I ≤ D)
    (hbalance : Module.finrank (ZMod 2) D + rank (Source.starImage H Uγ) =
      Module.finrank (ZMod 2) U)
    (hcodim : 1 < rank (Source.starImage H Uγ) →
      Module.finrank (ZMod 2) (U ⧸ I) ≤ 3)
    (hcomm : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (Source.starImage H Uγ)) ≤
      Module.finrank (ZMod 2) (D ⧸ I.comap D.subtype)) :
    rank (Source.starImage H Uγ) = 1 :=
  star_rank_one_of_dimension_balance H Uγ ρ
    (actor_faithful_of_noncentral_quotient e ρ f hf heq hnc)
    (Or.inr ⟨e⟩) hUγ D I hID hbalance hcodim hcomm

omit [Module.Finite (ZMod 2) W] in
/-- For A₆ the quadratic radical bound gives the stronger order bound two
on Vγ*, hence rank one on its nontrivial subgroup Uγ*. The actual γ-to-α
conjugator is retained. No intersection-codimension estimate is needed. -/
theorem alternating_star_rank_one_of_marked_quotient
    (H Uγ Vγ Vα : Subgroup G)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (f : P →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rhoA (e g) v) = ρ g (f v))
    (hnc : ∃ g v, ρ g v ≠ v)
    (hq : IsQuadratic ρ (Source.starImage H Vα))
    (hV : (Source.starImage H Vα).map e.toMonoidHom ≤ alternatingRadical)
    (c : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj c).toMonoidHom =
      Source.starImage H Vα)
    (hUV : Source.starImage H Uγ ≤ Source.starImage H Vγ)
    (hUγ : IsElementaryTwo (Source.starImage H Uγ)) :
    Nat.card (Source.starImage H Vγ) ≤ 2 ∧ rank (Source.starImage H Uγ) = 1 := by
  have hcard := MarkedQuotient.alternating_card_le_two H Vα e ρ f hf heq hnc hq hV
  rw [← hconj, Subgroup.card_map_of_injective (MulAut.conj c).injective] at hcard
  have hUcard := (Subgroup.card_le_of_le hUV).trans hcard
  have hr := Nat.log_monotone (b := 2) hUcard
  have hp := hUγ.rank_pos
  refine ⟨hcard, ?_⟩
  change Nat.log 2 (Nat.card (Source.starImage H Uγ)) = 1
  change 0 < Nat.log 2 (Nat.card (Source.starImage H Uγ)) at hp
  norm_num at hr
  omega
end CFSG.Quasithin.Chapter13.Section08.A6Endgame

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame
open Subgroup Representation.BinaryOffender
open CriticalGeometry CriticalGeometry.SectionActions
open CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
open IntersectionBalance
open ComponentSieve.SixAndG2.NaturalSix
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.SixLetterRadicalDisplacement.PermutationQuotients
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem tilde_conjugation (H V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) Z)
    (hz : H ≤ normalizer (Z : Set G)) (h : H) :
    tildeRepresentation H _ Z a (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (uAction H V₃ Z hz h)).toLinearMap := by
  ext v
  change Additive.ofMul (a.action (QuotientGroup.mk' (pCore 2 H) h) v.toMul) =
    Additive.ofMul (uAction H V₃ Z hz h v.toMul)
  congr 1
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (Source.UH H V₃)) v.toMul
  rw [← hu, a.conjugation]
  exact (quotientAction_apply H (Source.UH H V₃) Z _ hz h u).symm

/-- Aschbacher–Smith 13.8.34, with the genuine earlier local conclusions
explicit. The residual is O²(H∩M), and the case-two placement from 13.8.8
is in O₂(H∩M). A single actor equivalence marks the source plane parabolic
and, in the symmetric branch, the actual natural/augmentation module and
V₃ image. The quotient surjection, core marking, both rank bounds and both
line containments are deductions, not inputs.

`hproper`, `hDproper`, `hcomparison`, `hαU`, `hαV` and `hVcore` are the
case-two conclusions of 13.8.8 selected after 13.8.33. The source 13.7,
13.8.4 and F.9 inputs, and the generation premise used by 13.8.9 at the
original and reversed critical pair, remain for the section assembly owner.
The conjugations use Lean's left-conjugation convention. -/
theorem lemma_13_8_34
    {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (M L₁ V₃ Z Uα Vα : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃V : V₃ ≤ V) (hflag : V₃.relIndex V = 2) (hVH : V ≤ H)
    (hZU : Z ≤ Source.UH H V₃) (hZ : Nat.card Z = 2)
    (hz : H ≤ normalizer (Z : Set G))
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hbaseKernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) Z)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (hres : L₁ = (pResidual 2 ↥(H ⊓ M)).map (H ⊓ M).subtype)
    (hb : 3 ≤ c.path.length)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hVγH : c.Vgamma ≤ H)
    (hVHJ : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hVQ : Source.VH H V ≤ Source.QH H)
    (hedge : ⁅(L ⊔ T) ⊓ H, V⁆ ≤ Source.UH H V₃)
    (hgen : ∀ d : CriticalPair L T H V,
      (d = c ∨ ∃ r : Reversal c, d = r.pair) →
      Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ →
      vertexGroup L T H d.gamma =
        conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃)
    (hDproper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃)
    (hcomparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃))
    (h : H)
    (hαU : (c.Ugamma V₃).map (MulAut.conj (h : G)).toMonoidHom = Uα)
    (hαV : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hVcore : Vα ≤ (H ⊓ M).pCoreIn 2)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) Z)
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ)
    (hquadratic : IsQuadratic σ (Source.starImage H Vα))
    (models :
      (∃ e : Source.Hstar H ≃* alternatingGroup (Fin 6),
        (Source.starImage H (H ⊓ M)).map e.toMonoidHom =
          Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer) ∨
      (∃ e : Source.Hstar H ≃* S,
        (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2 ∧
        CompatibleModel H V₃ Z a e)) :
    (c.Aone Z ≤ Source.UH H V₃ ∧ Z ≤ c.Ugamma V₃) ∧
    rank (Source.starImage H (c.Ugamma V₃)) = 1 ∧
    (¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα) ∧
    rank (Source.starImage H c.Vgamma) ≤ 2 := by
  classical
  let _ := Fintype.ofFinite (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) :=
    LineContainments.EndpointSource.elementary_Ugamma c V₃
  have hUVγ : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃V le_rfl)
  have hγH := hUVγ.trans hVγH
  have hUVα : Uα ≤ Vα := by rw [← hαU, ← hαV]; exact map_mono hUVγ
  have hαH := hUVα.trans (hVcore.trans ((pCoreIn_le 2 _).trans inf_le_left))
  have hkernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z =
      c.Ugamma V₃ ⊓ Source.QH H := by
    rw [hbaseKernel]
    apply le_antisymm
    · refine le_inf (commutatorPreimage_le _ _ _) ?_
      exact le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hγH)
        (commutator_commutatorPreimage_le _ _ _ (hγH.trans hz))
    · exact le_commutatorPreimage inf_le_left
        ((commutator_mono inf_le_right le_rfl).trans
          (commutator_commutatorPreimage_le _ _ _ hz))
  have hUstar : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) :=
    ⟨starImage_ne_bot_of_Dgamma_lt H _ _ Z hγH hkernel hDproper,
      starImage_isElementaryAbelian H _ hγH⟩
  have hconj : (Source.starImage H c.Vgamma).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom =
      Source.starImage H Vα := by
    rw [← MarkedGeometry.starImage_conjugate c.Vgamma hVγH h, hαV]
  have hVR : Source.starImage H Vα ≤ Source.starImage H ((H ⊓ M).pCoreIn 2) :=
    map_mono (subgroupOf_mono H hVcore)
  have hτ := tilde_conjugation H V₃ Z a hz
  have hmodels : LineContainments.MarkedSourceModels H M V₃ Z
      (tildeRepresentation H _ Z a) := by
    rcases models with ⟨e, he⟩ | ⟨e, he, hm⟩
    · exact Or.inl ⟨e, he⟩
    · exact Or.inr ⟨e, he, CompatibleModel.action_cases H V₃ Z a e hm⟩
  have hranks : rank (Source.starImage H (c.Ugamma V₃)) = 1 ∧
      (¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα) ∧
      rank (Source.starImage H c.Vgamma) ≤ 2 := by
    rcases models with ⟨e, he⟩ | ⟨e, he, hm⟩
    · obtain ⟨f, hf, heq, hnc, _⟩ :=
        MarkedQuotient.alternating_source H M V V₃ e he hV₃V hflag hnoncentral hnorm σ hσ
      have hcore := SourceResidual.alternating_core H M L₁ hres e he
      have hnot := MarkedQuotient.alternating_core_not_le H L₁ Vα e σ f hf heq hnc hcore hquadratic
      have hR := SourceResidual.alternating_parabolic_core H M e he
      have hVA : (Source.starImage H Vα).map e.toMonoidHom ≤ alternatingRadical := by
        rw [← hR]; exact map_mono hVR
      obtain ⟨hc, hr⟩ := alternating_star_rank_one_of_marked_quotient H _ c.Vgamma Vα
        e σ f hf heq hnc hquadratic hVA _ hconj
        (map_mono (subgroupOf_mono H hUVγ)) hUstar
      refine ⟨hr, hnot, ?_⟩
      have hh := Nat.log_monotone (b := 2) hc
      change rank (Source.starImage H c.Vgamma) ≤ 1 at hh
      omega
    · obtain ⟨f, hf, heq, hnc, hfaithful⟩ :=
        MarkedQuotient.symmetric_source H M V V₃ e he hV₃V hflag hnoncentral hnorm σ hσ
      have hcore := SourceResidual.symmetric_core H M L₁ hres e he
      have hnot := MarkedQuotient.symmetric_core_not_le H L₁ Vα e σ f hf heq hnc hcore hquadratic
      have hR := SourceResidual.symmetric_parabolic_core H M e he
      have hcoreR : (Source.starImage H L₁).pCoreIn 2 ≤
          Source.starImage H ((H ⊓ M).pCoreIn 2) := by
        apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
        rw [hcore, hR]
        exact inf_le_left
      have hRcard : Nat.card (Source.starImage H ((H ⊓ M).pCoreIn 2)) ≤ 8 := by
        rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hR, D_card]
      have hVrank := star_rank_le_two_of_marked_noncontainment H L₁ Vα c.Vgamma _ _
        hconj hVR hcoreR hRcard hnot
      have hnγ := hVHJ.trans (c.normalizes_Ugamma V₃)
      have hn : Source.UH H V₃ ≤ normalizer (Uα : Set G) := by
        have hnU := (conjugateSpanBy_mono hV₃V le_rfl).trans hnγ
        have hmap := (map_mono (f := (MulAut.conj (h : G)).toMonoidHom) hnU).trans
          (le_normalizer_map _)
        have hUH : (Source.UH H V₃).map (MulAut.conj (h : G)).toMonoidHom =
            Source.UH H V₃ :=
          mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H h.property)
        change (Source.UH H V₃).map (MulAut.conj (h : G)).toMonoidHom ≤ _ at hmap
        rw [hαU, hUH] at hmap
        exact hmap
      obtain ⟨_, _, hID, hbalance, _, hcomm, hlarge⟩ :=
        source_intersection_and_dimension_balance H M V V₃ Z Uα (c.Ugamma V₃) Vα
          ((H ⊓ M).pCoreIn 2) a e hm hZU hZ he hV₃V hflag hnoncentral hnorm σ hσ
          hquadratic (map_mono (subgroupOf_mono H hUVα)) hVR hR (hαH.trans hz) hn
          h hαU (c.gb : G) rfl hγH hnγ hVQ hkernel
      have hr := star_rank_one_of_dimension_balance H (c.Ugamma V₃) σ hfaithful
        (Or.inr ⟨e⟩) hUstar (Dspace (Source.UH H V₃) (c.Ugamma V₃) Z)
        (Ispace (Source.UH H V₃) (c.Ugamma V₃)) hID hbalance
        (fun hr => (hlarge hr).2.2.2.2.1) hcomm
      exact ⟨hr, hnot, hVrank⟩
  exact ⟨LineContainments.line_containments_of_star_rank_one c M V₃ Z hV₃V hflag hVH
    hZU hZ hz hHC hbaseKernel hnoncentral hnorm hb hF915 hVγH hVHJ hedge hgen
    hproper hcomparison hranks.1 (tildeRepresentation H _ Z a) hτ σ hσ hmodels, hranks⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame
