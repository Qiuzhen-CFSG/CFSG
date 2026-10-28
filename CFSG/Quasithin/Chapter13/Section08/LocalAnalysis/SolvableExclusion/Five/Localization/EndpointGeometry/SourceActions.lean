module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport

/-!
# Comparing the supplied star action with the source section actions

Conjugation on representatives identifies the explicit `StarAction` with
`uStarAction`. The full earlier 13.8.5 output supplies its actual C-component
and product decomposition, so solvability excludes every nonidentity quotient
transvection. A common-axis action descends through the literal quotient;
strictness of its commutator-preimage denominator then excludes that action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.5(1), 13.8.10–11 and 13.8.13, printed pp.947, 950–951.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
open CriticalGeometry CriticalGeometry.Reorientation CriticalGeometry.SectionActions
open CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G] {H U Z : Subgroup G}
variable [IsElementaryAbelian 2 U]

/-- The supplied star action, restricted along the actual quotient map. -/
def centerAction (a : StarAction H U Z) : CenterQuotientAction H U Z where
  normalizes := a.normalizes
  action := a.action.comp (QuotientGroup.mk' (pCore 2 H))
  apply_mk := a.conjugation

/-- The full earlier model conclusion supplies precisely the component clause. -/
theorem component_conclusion_of_full {L L₁ T : Subgroup G}
    (a : StarAction H U Z) (hL₁ : L₁ ≤ H)
    (h135 : (∃ h : H, (centerAction a).action h ≠ 1 ∧
      binaryLinear ((centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) →
      FullModelConclusions L L₁ T hL₁ (centerAction a)) :
    TransvectionComponentConclusion a T := by
  intro t hn ht
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) t
  obtain ⟨K, hK, hKT⟩ := (h135 ⟨h, hn, ht⟩).1
  refine ⟨K, hK, ?_⟩
  rw [sup_eq_closure_mul, ← hKT, closure_eq]

/-- Uniqueness on representatives identifies the supplied action with the
literal action used by the critical-geometry lemmas. -/
theorem starAction_eq_uStar {V₃ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) Z)
    (hz : H ≤ normalizer (Z : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ Z) :
    a.action = uStarAction H V₃ Z hz hQ := by
  apply MonoidHom.ext
  intro t
  apply MulEquiv.ext
  intro w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) t
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (Source.UH H V₃)) w
  rw [a.conjugation, uStarAction_mk]
  exact (quotientAction_apply H (Source.UH H V₃) Z _ hz h u).symm

/-- The solvable exclusion applies to the literal uStarAction. -/
theorem no_uStar_transvection {V₃ T : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) Z)
    (hz : H ≤ normalizer (Z : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ Z)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T) :
    ∀ h : Source.Hstar H, uStarAction H V₃ Z hz hQ h ≠ 1 →
      binaryLinear (uStarAction H V₃ Z hz hQ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ Z)) := by
  rw [← starAction_eq_uStar a hz hQ]
  intro h hn ht
  exact hn (a.eq_one_of_transvection_of_solvable T hs h135 h ht)

/-- A common-axis action on U descends to U/Z. Source 13.8.5(1) makes
all those quotient actions trivial, contradicting the strict centralizer. -/
theorem no_axis_on_base {P D T : Subgroup G}
    (a : StarAction H U Z) (hPH : P ≤ H)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hproper : Source.Dgamma P U Z < P) :
    ¬ HasTransvectionAxis P U D (hPH.trans a.normalizes) := by
  intro haxis
  have hall (p : P) : a.action (QuotientGroup.mk' (pCore 2 H) (inclusion hPH p)) = 1 := by
    let q := QuotientGroup.mk' (Z.subgroupOf U)
    have hi (w : Additive U) :
        binaryMap q (binaryLinear (conjugationAction P U (hPH.trans a.normalizes) p) w) =
          binaryLinear (a.action (QuotientGroup.mk' (pCore 2 H) (inclusion hPH p)))
            (binaryMap q w) := (a.conjugation (inclusion hPH p) w.toMul).symm
    exact a.eq_one_of_transvection_of_solvable T hs h135 _
      (CriticalGeometry.SectionActions.transvection_of_surjective_intertwiner (binaryMap q)
        (QuotientGroup.mk'_surjective (Z.subgroupOf U)) _ _ hi (haxis.2.2 p))
  apply hproper.not_ge
  apply le_commutatorPreimage le_rfl
  apply commutator_le.mpr
  intro p hp u hu
  have he := a.conjugation (inclusion hPH ⟨p, hp⟩) ⟨u, hu⟩
  rw [hall ⟨p, hp⟩, MulAut.one_apply] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
  change (p * u * p⁻¹) / u ∈ Z at hh
  simpa only [div_eq_mul_inv, commutatorElement_def] using hh

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
end
