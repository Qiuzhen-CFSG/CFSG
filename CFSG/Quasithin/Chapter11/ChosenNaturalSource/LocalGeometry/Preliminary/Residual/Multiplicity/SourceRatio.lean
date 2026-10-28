module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.Ratio

/-!
# Exact ratio data on the original chosen natural actions

The literal central-quotient action has quadratic ratio one half. The
same hyperplane actor embeds in the faithful image of the actual LT action
on that quotient, so its cubic ratio is at most one half as well. Thus the
D.3.9 expression 2/q-hat is at least four on precisely this marked action;
it cannot be replaced by two using a lower bound of one for q-hat.

The full normalizer orbit admits a faithful representation of the original
L/O₂(L), whose action at each quotient representative is the original
conjugation action. Its quadratic ratio is exactly s/2, where its binary
dimension is 3ns. These are conclusions on the original D and S, without
an extra ratio or splitting premise. The small repeated-natural model in
`Ratio` explains why the numerical information alone does not exclude s=3.
It does not realize that model in the simple QTKE ambient group.

Unconditional cubic containment in 11.0.4 remains with
qt-d-1222-natural-preliminary-source. Its proof must use further ambient
information or select a natural constituent directly; the existing strict
bound and one/two-copy consumers retain their explicit hypotheses.
Source: Aschbacher--Smith, D.3.9, pp.199--200; A.3.19, pp.54--55;
and 11.0.3--4, p.760, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups ENNReal IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original marking gives the exact half-ratio on V/C_V(L). -/
theorem sl3_centralQuotient_quadraticRatio
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    quadraticRatio D.centralQuotientAction = 1 / 2 := by
  have h := ChapterK.Linear.Natural.quadraticRatio_eq S.field 3 (by decide)
  have he : quadraticRatio D.centralQuotientAction = quadraticRatio (linearNatural S.field 3) := by
    apply le_antisymm
    · exact quadraticRatio_le_of_injective_equivariant _ _ m.groupEquiv.symm.toMonoidHom
        m.groupEquiv.symm.injective m.linearEquiv.symm (by
          intro g v
          apply m.linearEquiv.injective
          rw [m.linearEquiv.apply_symm_apply]
          change (linearNatural S.field 3) g v =
            m.linearEquiv (D.centralQuotientAction (m.groupEquiv.symm g) (m.linearEquiv.symm v))
          simpa only [m.linearEquiv.apply_symm_apply,m.groupEquiv.apply_symm_apply] using
            (m.intertwines (m.groupEquiv.symm g) (m.linearEquiv.symm v)).symm)
    · exact quadraticRatio_le_of_injective_equivariant _ _ m.groupEquiv.toMonoidHom
        m.groupEquiv.injective m.linearEquiv m.intertwines
  simpa using he.trans h

/-- The literal component quotient already has a cubic actor of half ratio. -/
theorem sl3_centralQuotient_cubicRatio_le_half
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    cubicRatio D.centralQuotientAction ≤ 1 / 2 :=
  (cubicRatio_le_quadraticRatio _).trans_eq (sl3_centralQuotient_quadraticRatio D S m)

/-- The proposed lower bound of one fails on the original component action. -/
theorem sl3_centralQuotient_not_one_le_cubicRatio
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    ¬ 1 ≤ cubicRatio D.centralQuotientAction := by
  intro h
  have := h.trans (sl3_centralQuotient_cubicRatio_le_half D S m)
  norm_num at this
/-- The actual faithful LT action on the original quotient has ratio at most
one half. The quotient and natural marking are the source maps. -/
theorem sl3_localJoin_cubicRatio_le_half
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    cubicRatio (imageRepresentation ((Coordinates.sl3 m).conjugationAction
      (sup_le L.le_normalizer D.sylow_normalizes_component)
      (sup_le D.normalizes S.sylow_normalizes))) ≤ 1 / 2 := by
  let J := L ⊔ (T : Subgroup G)
  let c := Coordinates.sl3 m
  let i : L →* J := inclusion le_sup_left
  let η := m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  apply NaturalMultiplicity.cubicRatio_le_half_of_natural_quotient S.field _ i η
    (m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    (LinearEquiv.refl _ _)
  intro l w
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
  have hw : (c.projection v).toAdd = w := congrArg Multiplicative.toAdd hv
  rw [← hw]
  change c.conjugationAction _ _ (i l) _ = _
  rw [c.conjugationAction_projection]
  have he : V.normalizerMonoidHom
      (inclusion (sup_le D.normalizes S.sylow_normalizes) (i l)) v =
      V.normalizerMonoidHom (inclusion D.normalizes l) v := rfl
  rw [he,c.projection_component_conjugation]
  rfl

/-- The lower bound needed to turn 2/q-hat into two is false for the
literal LT action occurring in D.3.9. -/
theorem sl3_localJoin_not_one_le_cubicRatio
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    ¬ 1 ≤ cubicRatio (imageRepresentation ((Coordinates.sl3 m).conjugationAction
      (sup_le L.le_normalizer D.sylow_normalizes_component)
      (sup_le D.normalizes S.sylow_normalizes))) := by
  intro h
  have := h.trans (sl3_localJoin_cubicRatio_le_half D S m)
  norm_num at this

/-- The full orbit action factors faithfully through the original two-core
quotient, with exact quadratic ratio s/2. The representative equation fixes
its relation to the actual conjugation action. -/
theorem FullModuleNaturalCopies.component_ratio
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)} {s : ℕ}
    (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) :
    letI := fullModule_elementary D S
    ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L)
        (Additive (componentOrbit V (normalizer (L : Set G)))),
      Function.Injective σ ∧
      (∀ l v, σ (QuotientGroup.mk' (pCore 2 L) l) v =
        fullModuleConjugation D S (inclusion L.le_normalizer l) v) ∧
      quadraticRatio σ = s / 2 := by
  let := fullModule_elementary D S
  obtain ⟨e,he⟩ := h
  let μ := repeated (linearNatural S.field 3) s
  let σ := e.symm.conjRingEquiv.toMonoidHom.comp (μ.comp m.groupEquiv.toMonoidHom)
  have hact (g : L ⧸ pCore 2 L) (v) : e (σ g v) = μ (m.groupEquiv g) (e v) := by
    change e (e.symm (μ (m.groupEquiv g) (e v))) = _
    exact e.apply_symm_apply _
  refine ⟨σ,e.symm.conjRingEquiv.injective.comp
    ((NaturalMultiplicity.natural_repeated_faithful S.field hs).comp m.groupEquiv.injective),
    ?_,?_⟩
  · intro l v
    apply e.injective
    rw [hact,he]
    rfl
  · have hq : quadraticRatio σ = quadraticRatio μ := by
      apply le_antisymm
      · exact quadraticRatio_le_of_injective_equivariant μ σ
          m.groupEquiv.symm.toMonoidHom m.groupEquiv.symm.injective e.symm (by
            intro g v
            apply e.injective
            rw [e.apply_symm_apply,hact,e.apply_symm_apply]
            change μ g v = μ (m.groupEquiv (m.groupEquiv.symm g)) v
            rw [m.groupEquiv.apply_symm_apply])
      · exact quadraticRatio_le_of_injective_equivariant σ μ
          m.groupEquiv.toMonoidHom m.groupEquiv.injective e hact
    exact hq.trans (NaturalMultiplicity.natural_quadraticRatio S.field hs)

/-- Actual full-orbit ratio and dimension coordinates on D and S, with all
marking and quotient-action premises discharged. -/
theorem fullModule_sl3_component_ratio
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    ∃ s : ℕ, 0 < s ∧
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L)
          (Additive (componentOrbit V (normalizer (L : Set G)))),
        Function.Injective σ ∧
        (∀ l v, σ (QuotientGroup.mk' (pCore 2 L) l) v =
          fullModuleConjugation D S (inclusion L.le_normalizer l) v) ∧
        quadraticRatio σ = s / 2 ∧
        Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) =
          s * (3 * S.field.degree) := by
  let := fullModule_elementary D S
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  obtain ⟨σ,hf,ha,hq⟩ := h.component_ratio D S hs
  exact ⟨s,hs,σ,hf,ha,hq,h.finrank⟩


/-- On the exact source LT action, the D.3.9 upper-bound expression is
at least four. This is a diagnostic about that expression, not an assertion
that the full orbit has four copies. -/
theorem sl3_localJoin_four_le_two_div_cubicRatio
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    4 ≤ 2 / cubicRatio (imageRepresentation ((Coordinates.sl3 m).conjugationAction
      (sup_le L.le_normalizer D.sylow_normalizes_component)
      (sup_le D.normalizes S.sylow_normalizes))) := by
  calc
    4 = 2 / (1 / 2 : ℝ≥0∞) := by norm_num [div_eq_mul_inv]
    _ ≤ _ := ENNReal.div_le_div_left (sl3_localJoin_cubicRatio_le_half D S m) 2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
