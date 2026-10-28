module

public import Theory.SpecificGroups.Monster.Construction.GriessCarrier
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Splitting

/-!
# The fixed octad carrier and its source forms

The carrier is the existing octad span in the signed short-lift space, and
its inclusion is the restriction of the short inclusion into the fixed Griess
space. Thus its positive form and cubic form are the restrictions of the
actual forms of Section 28. In particular the cubic is `shortCubic`, with
the central-product coefficient of (28.4), and has no new normalization.

The vectors retain the source conventions: complementing the even subset
fixes the vector, whereas changing the Parker-loop sign negates it.

Source: Aschbacher, *Sporadic Groups*, 27.8, 28.4 and 29.13(1), printed
pp. 150–151 and 160. This module constructs the carrier, not its N-action.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies Griess TrialitySpin
open Atlas.Codes Atlas.Fischer
attribute [local instance] Classical.propDecidable

/-- The literal source octad summand `B_Z`. -/
abbrev Space := ↥octadSpace

/-- Name the inherited structure to keep nested block-submodule inference small. -/
instance spaceAddCommGroup : AddCommGroup Space :=
  inferInstanceAs (AddCommGroup octadSpace)

/-- The inclusion in the fixed, parameter-free Griess space. -/
def inclusion : Space →ₗ[ℝ] GriessSpace :=
  (shortInclusion sourceLatticeComparison).comp octadSpace.subtype

@[simp] theorem inclusion_apply (v : Space) :
    inclusion v = shortInclusion sourceLatticeComparison v.val := rfl

theorem inclusion_injective : Function.Injective inclusion := by
  intro v w h
  exact Subtype.ext (congrArg (fun a : GriessSpace => a.2.1) h)

/-- The actual signed source vector, now in its octad summand. -/
def vector (p : OctadParameters) : Space :=
  ⟨shortVector sourceLatticeComparison (rOctad p), Submodule.subset_span ⟨p, rfl⟩⟩

@[simp] theorem vector_val (p : OctadParameters) :
    (vector p).val = shortVector sourceLatticeComparison (rOctad p) := rfl

theorem vector_complement (p : OctadParameters) : vector p.complement = vector p := by
  apply Subtype.ext
  simp only [vector_val, rOctad_complement]

theorem vector_sign (p : OctadParameters) : vector (p.sign 1) = -vector p := by
  apply Subtype.ext
  exact rOctad_vector_sign p

theorem vector_eq_iff (p q : OctadParameters) :
    vector p = vector q ↔ p.c = q.c ∧ (p.J = q.J ∨ p.J = q.J + q.c.1.val) := by
  have h : vector p = vector q ↔ rOctad p = rOctad q := by
    constructor
    · intro he
      exact (shortLiftSigns sourceLatticeComparison).delta_injective
        (congrArg Subtype.val he)
    · intro he
      apply Subtype.ext
      simp only [vector_val, he]
  exact h.trans (rOctad_eq_iff p q)

theorem vector_eq_neg_iff (p q : OctadParameters) :
    vector p = -vector q ↔
      p.c = parkerSign 1 q.c ∧ (p.J = q.J ∨ p.J = q.J + q.c.1.val) := by
  rw [← vector_sign, vector_eq_iff]
  rfl

theorem span_vectors : Submodule.span ℝ (Set.range vector) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff octadSpace
    (fun p => Submodule.subset_span (show shortVector sourceLatticeComparison (rOctad p) ∈
      summandGenerators .octad from ⟨p, rfl⟩))).mpr rfl

/-- Linear maps on `B_Z` can be checked on all actual source octad vectors. -/
theorem linearMap_ext {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f g : Space →ₗ[ℝ] V} (h : ∀ p, f (vector p) = g (vector p)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g span_vectors).mpr
  rintro ⟨_, p, rfl⟩
  exact h p

/-- The induced positive form, with unit source vectors. -/
def gamma : LinearMap.BilinForm ℝ Space :=
  (shortForm sourceLatticeComparison).compl₁₂ octadSpace.subtype octadSpace.subtype

@[simp] theorem gamma_apply (v w : Space) :
    gamma v w = shortForm sourceLatticeComparison v.val w.val := rfl

theorem gamma_inclusion (v w : Space) :
    griessGamma (inclusion v) (inclusion w) = gamma v w :=
  gamma_short sourceLatticeComparison v.val w.val

theorem gamma_symmetric (v w : Space) : gamma v w = gamma w v :=
  shortForm_symmetric sourceLatticeComparison v.val w.val

theorem gamma_pos (v : Space) (hv : v ≠ 0) : 0 < gamma v v :=
  shortForm_pos sourceLatticeComparison v.val (fun h => hv (Subtype.ext h))

theorem gamma_vector (p q : OctadParameters) :
    gamma (vector p) (vector q) =
      (if rOctad p = rOctad q then 1 else 0) -
        (if rOctad p = (shortLiftSigns sourceLatticeComparison).flip (rOctad q)
          then 1 else 0) := form_vector _ _

theorem gamma_vector_self (p : OctadParameters) : gamma (vector p) (vector p) = 1 := by
  rw [gamma_vector, if_pos rfl, if_neg, sub_zero]
  exact ((shortLiftSigns sourceLatticeComparison).fixedPointFree (rOctad p)).symm

/-- The exact cubic block, restricted in all three arguments. -/
def beta : Space →ₗ[ℝ] Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ :=
  pullback3 (V := Space) (shortCubic sourceLatticeComparison)
    octadSpace.subtype octadSpace.subtype octadSpace.subtype

@[simp] theorem beta_apply (v w u : Space) :
    beta v w u = shortCubic sourceLatticeComparison v.val w.val u.val := rfl

theorem beta_inclusion (v w u : Space) :
    griessBeta (inclusion v) (inclusion w) (inclusion u) = beta v w u :=
  sourceBeta_RRR sourceLatticeComparison v.val w.val u.val

theorem beta_vector (p q s : OctadParameters) :
    beta (vector p) (vector q) (vector s) =
      centralCoefficient ((rOctad p).val * (rOctad q).val * (rOctad s).val) :=
  shortCubic_vector sourceLatticeComparison _ _ _

theorem beta_vector_source (p q s : OctadParameters) :
    beta (vector p) (vector q) (vector s) =
      shortForm sourceLatticeComparison
        (shortSourceProduct sourceLatticeComparison (rOctad p) (rOctad q))
        (shortVector sourceLatticeComparison (rOctad s)) :=
  shortCubic_source sourceLatticeComparison _ _ _

theorem beta_swap_left (v w u : Space) : beta v w u = beta w v u :=
  shortCubic_swap_left sourceLatticeComparison v.val w.val u.val

theorem beta_swap_right (v w u : Space) : beta v w u = beta v u w :=
  shortCubic_swap_right sourceLatticeComparison v.val w.val u.val

end Sporadic.Monster.Construction.NOctad
