module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.Faithfulness
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.FirstSupport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.Lifting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.FactorNormalization
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.DiagonalComplement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Selection
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Constructing the second actor and locating the source line

`exists_secondFactor` constructs the actual B₂ inside Vγ and all the
starred product and action clauses from the faithful star action, ReducedFive,
the rank-one factors and the geometric bounds. It derives elementarity of
Vγ* from elementary V and abelian V_H (13.8.2), and derives its faithfulness
on P* from the parabolic-core placement in 13.8.8(2). The generation clause
of ReducedFive is the earlier consequence of minimality in the genuine Hz.

The support-kernel calculation normalizes every canonical five-factor.
The faithful diagonal action then forces exactly two factors and constructs
an order-two complement centralizing the first and moving the second.
Lifting that complement inside Vγ retains its exact starred image. Finally,
the order-two D_H index and inversion on the first factor place the actual
A₁ quotient image in the first support.

The earlier placement is expressed using left conjugation: the h supplied
here is the inverse of the source's right-conjugating element. The parent
localization construction supplies the geometric bounds and the earlier
source inputs; this module does not assert the full solvable-overgroup
exclusion of 13.8.13.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the final two paragraphs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
open Subgroup CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {L T H V V₃ V₁ P : Subgroup G}
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
variable [IsMulCommutative (Source.UH H V₃)]
variable [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Lift a constructed starred complement inside Vγ and supply the source
line clause from the geometric bounds and first-factor normalization. -/
theorem of_star_complement
    (c : CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁) (hf : Function.Injective a.action)
    (f : RankOneFactors a P (c.Ugamma V₃)) (geo : GeometricBounds c V₃ V₁)
    (hcount : f.factors.count = 2) (i : Fin f.factors.count) (hi : i.val ≠ 0)
    (B : Subgroup (Source.Hstar H)) (hB : B ≤ Source.starImage H c.Vgamma)
    (hcard : Nat.card B = 2)
    (hproduct : Source.starImage H c.Vgamma = Source.starImage H (c.Ugamma V₃) ⊔ B)
    (hdisjoint : Disjoint (Source.starImage H (c.Ugamma V₃)) B)
    (hcommute : ⁅Source.starImage H (c.Ugamma V₃), B⁆ = ⊥)
    (hfirst : ⁅B, Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩)⁆ = ⊥)
    (hsecond : ⁅B, Source.starImage H (f.factors.factor i)⁆ ≠ ⊥)
    (hnfirst : Source.starImage H (c.Ugamma V₃) ≤
      normalizer (Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩) : Set _))
    (hnsecond : Source.starImage H c.Vgamma ≤
      normalizer (Source.starImage H (f.factors.factor i) : Set _)) :
    Nonempty (SecondFactor a f c.Vgamma (c.Aone V₁)) := by
  have he := starImage_liftWithin H c.Vgamma B hB
  refine ⟨{
    count_eq_two := hcount
    second := i
    second_ne_zero := hi
    B₂ := liftWithin H c.Vgamma B
    B₂_le := liftWithin_le H c.Vgamma B
    star_card := by simpa only [he] using hcard
    star_product := by simpa only [he] using hproduct
    star_disjoint := by simpa only [he] using hdisjoint
    star_commute := by simpa only [he] using hcommute
    centralizes_first := by simpa only [he] using hfirst
    moves_second := by simpa only [he] using hsecond
    normalizes_second := hnsecond
    line_le_first := line_le_first a hf f geo.Ugamma_le geo.Aone_le
      geo.Aone_card geo.DH_index hnfirst }⟩

/-- Construct the second actor from the rank-one and geometric outputs of
13.8.13. The remaining standing inputs are V₃ ≤ V, elementary V, abelian V_H
from 13.8.2, and the conjugate-core placement from 13.8.8(2). Solvability and
minimal Hz membership are retained from the source setup; their generation
consequence is already supplied by ReducedFive. No factor normalization,
faithfulness on P*, factor count, complement or line containment is assumed. -/
theorem exists_secondFactor {L₁ M Vα G₁ : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    (c : CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁) (hf : Function.Injective a.action)
    (r : ReducedFive H L₁ T M Vα)
    (f : RankOneFactors a r.P (c.Ugamma V₃))
    (_hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (_hsolvable : Group.IsSolvable H)
    (geo : GeometricBounds c V₃ V₁) (hV₃ : V₃ ≤ V)
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Nonempty (SecondFactor a f c.Vgamma (c.Aone V₁)) := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono hV₃ le_rfl)
  let : IsElementaryAbelian 2 (Source.VH H V) := by
    let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x}) :=
      (inferInstance : IsMulCommutative (Source.VH H V))
    change IsElementaryAbelian 2 (closure {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x})
    apply IsElementaryAbelian.closure_of_isMulCommutative
    rintro x ⟨h, _, v, hv, rfl⟩
    rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]
  let : IsElementaryAbelian 2 c.Vgamma :=
    IsElementaryAbelian.map (MulAut.conj (c.gb : G)).toMonoidHom
  let : IsElementaryAbelian 2 (c.Vgamma.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf geo.Vgamma_le
  let : IsElementaryAbelian 2 (Source.starImage H c.Vgamma) :=
    IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 H))
  have hn := f.star_normalizes_factors a hf r.P_le r.Pstar_normal hUV
    geo.Vgamma_le inferInstance
  have hgen : Source.starImage H r.P =
      ⨆ i, Source.starImage H (f.factors.factor i) := by
    have he : r.P.subgroupOf H = ⨆ i, (f.factors.factor i).subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le r.P_le, Subgroup.map_iSup]
      calc
        r.P = ⨆ i, f.factors.factor i := f.factors.generated
        _ = ⨆ i, ((f.factors.factor i).subgroupOf H).map H.subtype := by
          congr 1
          funext i
          exact (map_subgroupOf_eq_of_le ((f.factors.factor_le i).trans r.P_le)).symm
    simp only [Source.starImage, he, Subgroup.map_iSup]
  obtain ⟨h, hh⟩ := hplacement
  have hfaith := star_faithful_on_P_of_core_placement r h hh
  rw [hgen] at hfaith
  obtain ⟨hcount, i, B, hi, hB, hcard, hprod, hdisj, hcomm, hfirst, hsecond⟩ :=
    DiagonalComplement.exists_complement f.factors.count_pos f.factors.count_le_two
      (fun i => Source.starImage H (f.factors.factor i)) f.factors.star_card
      (Source.starImage H c.Vgamma) (Source.starImage H (c.Ugamma V₃))
      (map_mono (subgroupOf_mono H hUV)) f.actor_card geo.Vgamma_star_card hn hfaith
      f.first_moved f.remaining_fixed
  exact of_star_complement c a hf f geo hcount i hi B hB hcard hprod hdisj hcomm
    hfirst hsecond ((map_mono (subgroupOf_mono H hUV)).trans (hn _)) (hn i)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
end
