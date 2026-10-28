module

public import CFSG.Quasithin.Chapter13.Section07.SeedCommutator
public import CFSG.Quasithin.Chapter13.Section05.LocalSteps
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The noncentral quotient in source13.7.7

Normal closure and the exact seed calculation give U_H=[V_H,O₂(H)]. If
[V_H,H] lay in U_H, each conjugate generator would lie in V U_H. The
commutator bounds would then force U_H≤V₃, contradicting the strict span
from13.5.5. The final source consumer constructs the seed equality using
the natural pairing and transports the original13.5.4(5) noncentrality.

Only genuine earlier13.5 applicability, abelian seed-span, normalizer
control and noncentrality remain explicit. Source: Aschbacher–Smith13.7.3(6)
and13.7.7, printed pp.936,940.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

/-- The last equality of13.7.3(6) follows from the genuine seed commutator
calculation and normality; no conclusion about the whole span is an input. -/
theorem UH_eq_commutator_QH (h : D.Hypothesis) (hseed : ⁅D.V, D.QH⁆ = D.Vplus) :
    D.UH = ⁅D.VH, D.QH⁆ := by
  have hHU : D.H ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy D.Vplus D.H
  have hHV : D.H ≤ normalizer (D.VH : Set G) := le_normalizer_conjugateSpanBy D.V D.H
  have hHQ := Hypothesis.H_normalizes_QH (D := D)
  have hHU' : D.H ≤ normalizer (⁅D.VH, D.QH⁆ : Subgroup G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHV hx),
      mem_normalizer_iff_map_conj_eq.mp (hHQ hx)]
  apply le_antisymm
  · apply conjugateSpanBy_le _ hHU'
    rw [← hseed]
    exact commutator_mono (le_conjugateSpanBy D.V D.H) le_rfl
  · have hV : D.V ≤ commutatorPreimage D.H D.QH D.UH :=
      le_commutatorPreimage h.V_le_H (hseed.le.trans (le_conjugateSpanBy D.Vplus D.H))
    have hspan : D.VH ≤ commutatorPreimage D.H D.QH D.UH :=
      conjugateSpanBy_le hV
        (commutatorPreimage_normalized _ _ _ _ hHU D.H.le_normalizer hHQ hHU)
    exact (commutator_mono hspan le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hHU)

/-- 13.7.7 from the strict seed span and the actual seed commutator equality. -/
theorem noncentral_VH_quotient (h : D.Hypothesis) (hVQ : D.V ≤ D.QH)
    (hseed : ⁅D.V, D.QH⁆ = D.Vplus) (hstrict : D.Vplus < D.UH) :
    ¬ ⁅D.VH, D.H⁆ ≤ D.UH := by
  intro hc
  have hspan : D.VH ≤ D.V ⊔ D.UH := by
    apply (closure_le _).mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change g * v * g⁻¹ ∈ D.V ⊔ D.UH
    have hcomm : ⁅g, v⁆ ∈ D.UH := by
      rw [commutator_comm] at hc
      exact hc (commutator_mem_commutator hg (le_conjugateSpanBy D.V D.H hv))
    have hh := (D.V ⊔ D.UH).mul_mem (mem_sup_right hcomm) (mem_sup_left hv)
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hQN : D.QH ≤ normalizer (D.Vplus : Set G) :=
    h.QH_le_T.trans (le_sup_right.trans h.local_normalizes)
  have hvK : D.V ≤ commutatorPreimage D.QH D.QH D.Vplus :=
    le_commutatorPreimage hVQ hseed.le
  have huK : D.UH ≤ commutatorPreimage D.QH D.QH D.Vplus :=
    le_commutatorPreimage h.UH_le_QH
      (h.commutator_UH_QH_le_point.trans h.point_lt.le)
  have hle : D.UH ≤ D.Vplus := by
    rw [UH_eq_commutator_QH h hseed]
    exact (commutator_mono (hspan.trans (sup_le hvK huK)) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQN)
  exact (not_le_of_gt hstrict) hle

/-- Literal source13.7.7:13.5.5 supplies strictness and the new natural
source family supplies V≤O₂(H), leaving only the exact13.7.3(6) seed calculation. -/
theorem source_noncentral_VH_quotient
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hout : ¬ H ≤ M)
    (hbound : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M)
    (hseed : ⁅V, Section08.Source.QH H⁆ = V₃) :
    ¬ ⁅Section08.Source.VH H V, H⁆ ≤ Section08.Source.UH H V₃ := by
  apply noncentral_VH_quotient h
    ((le_conjugateSpanBy V H).trans (VH_le_core d h hU)) hseed
  exact Section05.seed_lt_span V₁ V₃ H M
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hout hbound

/-- All actual commutator conclusions of13.7.3(6), with the original
13.5.4(5) noncentrality on G₁ rather than desired local equalities. -/
theorem source_commutator_conclusions
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hHG : H ≤ G₁) (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ⁅V, Section08.Source.QH H⁆ = V₃ ∧
    ⁅V₃, Section08.Source.QH H⁆ = V₁ ∧
    ⁅Section08.Source.UH H V₃, Section08.Source.QH H⁆ = V₁ ∧
    V₃ ⊓ centralizer (Section08.Source.QH H : Set G) = V₁ ∧
    ⁅Section08.Source.VH H V, Section08.Source.QH H⁆ = Section08.Source.UH H V₃ := by
  have hn := seed_noncentral_on_local_core h hHG hne
  have hs := commutator_V_QH_eq_seed d h hn
  have hp := seed_and_span_commutator_eq_line d h hn
  exact ⟨hs, hp.1, hp.2, seed_centralizer_eq_line d h hn,
    (UH_eq_commutator_QH h hs).symm⟩

/-- Literal13.7.7 with the seed identity discharged by the actual natural action. -/
theorem source_noncentral_VH_quotient_of_earlier_geometry
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hHG : H ≤ G₁) (hout : ¬ H ≤ M)
    (hbound : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M)
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ¬ ⁅Section08.Source.VH H V, H⁆ ≤ Section08.Source.UH H V₃ :=
  source_noncentral_VH_quotient d h hU hout hbound
    (source_commutator_conclusions d h hHG hne).1

end CFSG.Quasithin.Chapter13.Section07
