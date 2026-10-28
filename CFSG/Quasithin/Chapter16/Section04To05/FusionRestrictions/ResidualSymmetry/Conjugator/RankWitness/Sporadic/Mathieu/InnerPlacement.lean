module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Inner Mathieu actions with the full covering component retained

For M₁₁, M₂₃ and M₂₄ every model automorphism is inner. Faithfulness
of automorphisms of a perfect group on its central quotient lifts this
fact through the full center of L. Thus N_G(L) = C_G(L)L, which puts
the selected conjugate centralizer in Δ₀ using its actual relative
Sylow subgroup R. No Δ₀ hypothesis is added.

The inverse actor then factors as c*l, with c centralizing L and l in L.
Its image in L/Z(L) has order two; no assertion that l itself is an
involution is made. In the unequal-residual case that same model
involution fails to commute with an odd-order element of the actual
forward residual image. This supplies innerness and placement, not an
ambient odd-rank-three witness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(3),(6),(7), printed p.1171; Δ₀ and 16.4.2, p.1183;
and the selected actors in 16.5.6(3), p.1197.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
open CFSG.Quasithin.Chapter16
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic

private theorem model_conj_surjective (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24) :
    Function.Surjective (MulAut.conj : name.Carrier →* MulAut name.Carrier) := by
  rcases hn with rfl | rfl | rfl
  · exact fun a => _root_.Sporadic.Mathieu.m11_automorphism_inner a
  · exact _root_.Sporadic.Mathieu.m23_conj_surjective
  · exact _root_.Sporadic.Mathieu.M24OuterRestriction.conj_surjective

variable {G : Type*} [Group G] {L : Subgroup G}

/-- Every action on the full covering component is inner. -/
theorem innerMathieu_action_inner [IsQuasisimple L]
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier) (a : MulAut L) :
    ∃ l : L, a = MulAut.conj l := by
  apply (MulAut.centralQuotientAction_inner_iff e a).mp
  obtain ⟨s, hs⟩ := model_conj_surjective name hn (MulAut.centralQuotientAction e a)
  exact ⟨s, hs.symm⟩

/-- Innerness identifies the actual ambient normalizer. -/
theorem innerMathieu_normalizer_eq [IsQuasisimple L]
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier) :
    normalizer (L : Set G) = centralizer (L : Set G) ⊔ L := by
  apply le_antisymm
  · intro x hx
    obtain ⟨l, hl⟩ := innerMathieu_action_inner name hn e
      (L.normalizerMonoidHom ⟨x, hx⟩)
    have hm : (⟨x, hx⟩ : normalizer (L : Set G)) ∈
        (MulAut.conj : L →* MulAut L).range.comap L.normalizerMonoidHom :=
      ⟨l, hl.symm⟩
    rw [normalizerMonoidHom_comap_conj_range] at hm
    simpa only [mem_subgroupOf, sup_comm] using hm
  · exact sup_le (centralizer_le_normalizer _) L.le_normalizer

variable [Finite G] {T : Sylow 2 G} {z g : G} {R : Subgroup G}

/-- The genuine relative Sylow subgroup witnesses Δ₀ membership. -/
theorem innerMathieu_mem_deltaZero (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier) :
    (centralizer (L : Set G)).conjBy g ∈ deltaZero L := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  refine ⟨d.setup.mem_delta, R, d.setup.sylow, ?_⟩
  rw [← innerMathieu_normalizer_eq name hn e]
  exact (omegaOneAmbient_le R).trans (d.setup.le_sylow.trans d.setup.sylow_normalizes)

/-- Lift the inverse action, keeping order two on the central quotient. -/
theorem innerMathieu_inverse_lift (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ l : L, L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩ =
      MulAut.conj l ∧ orderOf (modelProjection e l) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨l, hl⟩ := innerMathieu_action_inner name hn e
    (L.normalizerMonoidHom ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩)
  refine ⟨l, hl, ?_⟩
  change orderOf (e (QuotientGroup.mk' (center L) l)) = 2
  rw [e.orderOf_eq, ← orderOf_injective quotientConj quotientConj_injective,
    quotientConj_mk, ← hl]
  exact d.inverse_action_order hne

/-- Factor the specified inverse actor without changing the conjugator. -/
theorem innerMathieu_inverse_factorization (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ (l : L) (c : G), c ∈ centralizer (L : Set G) ∧
      MulAut.conj g⁻¹ z = c * l ∧ orderOf (modelProjection e l) = 2 ∧
      inverseModelAction d e = MulAut.conj (modelProjection e l) := by
  obtain ⟨l, hl, ho⟩ := innerMathieu_inverse_lift d name hn e hne
  let a : normalizer (L : Set G) := ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
  let b : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  have hb : L.normalizerMonoidHom b = MulAut.conj l := by ext x; rfl
  have hk : a * b⁻¹ ∈ L.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb]
    change L.normalizerMonoidHom a * (MulAut.conj l)⁻¹ = 1
    rw [show L.normalizerMonoidHom a = MulAut.conj l from hl, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  refine ⟨l, MulAut.conj g⁻¹ z * (l : G)⁻¹, hk, ?_, ho, ?_⟩
  · group
  · change MulAut.centralQuotientAction e (L.normalizerMonoidHom a) = _
    rw [show L.normalizerMonoidHom a = MulAut.conj l from hl]
    exact MulAut.centralQuotientAction_conj e l

/-- The actual inverse model involution moves an odd residual element. -/
theorem innerMathieu_exists_noncommuting_odd_element
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ center L ≃* name.Carrier)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ∃ b : name.Carrier, orderOf b = 2 ∧ inverseModelAction d e = MulAut.conj b ∧
      ∃ x ∈ residualImage e (MulAut.conj g z), Odd (orderOf x) ∧ b * x ≠ x * b := by
  obtain ⟨l, _, _, _, hl, ha⟩ := innerMathieu_inverse_factorization d name hn e hne
  obtain ⟨x, hx, ho, hmove⟩ := exists_moved_odd_model_element hG d e hne
  refine ⟨modelProjection e l, hl, ha, x, hx, ho, ?_⟩
  intro he
  apply hmove
  rw [ha]
  change modelProjection e l * x * (modelProjection e l)⁻¹ = x
  rw [he, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
