module
public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.Representation.G2OrthogonalCover.BinaryFusion
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The full normalizer of the binary G₂ Weyl cover

A linear automorphism fixing the scalar identity and normalizing the derived
G₂ action descends to the natural six-space. Its operator there is an actual
G₂(2) element. Both operators preserve the octonion norm, so uniqueness of a
singular representative in each scalar fiber identifies them on the entire
seven-space. The covering center is retained throughout.

Source: Aschbacher--Smith B.4.6(1), printed pp.88--90, used in 12.4.9,
printed p.816; the binary natural normalizer and Weyl norm calculations
are supplied by the imported modules.
-/

open Representation Representation.OneCohomology Representation.BinaryOffender
namespace Atlas.G2.Natural.OrthogonalCover
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => _root_.commutator (Model F)
local notation "N" => Space F

@[expose] public noncomputable section

/-- Every scalar-fixing linear normalizer of the actual derived Weyl action
is a full binary G₂ operator on the original seven-space. -/
theorem normalizing_equiv_eq_traceZeroAction
    (a : E ≃ₗ[F] E)
    (hai : a (identity F) = identity F)
    (han : ∀ d : D, ∃ d' : D, ∀ x, a (action F d x) = action F d' (a x)) :
    ∃ g : Model F, ∀ x, a x = traceZeroAction F g x := by
  let q : E →ₗ[F] N := mk F
  have hk : q.ker ≤ (q.comp a.toLinearMap).ker := by
    intro x hx
    have hx' : x ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp hx
    rcases (binary_scalar_iff x).mp hx' with rfl | rfl
    · simp
    · change mk F (a (identity F)) = 0
      rw [hai]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)
  let b : N →ₗ[F] N :=
    (q.ker.liftQ (q.comp a.toLinearMap) hk).comp
      (q.quotKerEquivOfSurjective (mk_surjective F)).symm.toLinearMap
  have hb (x : E) : b (mk F x) = mk F (a x) := by
    change (q.ker.liftQ (q.comp a.toLinearMap) hk)
      ((q.quotKerEquivOfSurjective (mk_surjective F)).symm (q x)) = q (a x)
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hbs : Function.Surjective b := by
    intro v
    obtain ⟨x,rfl⟩ := mk_surjective F v
    exact ⟨mk F (a.symm x),by rw [hb,a.apply_symm_apply]⟩
  let B : N ≃ₗ[F] N := LinearEquiv.ofBijective b
    ⟨LinearMap.injective_iff_surjective.mpr hbs,hbs⟩
  let u : (Module.End F N)ˣ := LinearMap.GeneralLinearGroup.ofLinearEquiv B
  have hu (d : D) : ∃ d' : D, u * (derivedAction F).asGroupHom d * u⁻¹ =
      (derivedAction F).asGroupHom d' := by
    obtain ⟨d',hd'⟩ := han d
    refine ⟨d',Units.ext (LinearMap.ext fun v => ?_)⟩
    obtain ⟨x,hx⟩ := mk_surjective F (B.symm v)
    have he : v = B (mk F x) := by rw [hx,B.apply_symm_apply]
    rw [he]
    change B (derivedAction F d (B.symm (B (mk F x)))) =
      derivedAction F d' (B (mk F x))
    rw [B.symm_apply_apply]
    change b (derivedAction F d (mk F x)) = derivedAction F d' (b (mk F x))
    rw [derivedAction_mk,hb,hb,derivedAction_mk]
    exact congrArg (mk F) (hd' x)
  have hnorm : u ∈ linearNormalizer (derivedAction F) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hle : (actionImage (derivedAction F)).map (MulAut.conj u).toMonoidHom ≤
        actionImage (derivedAction F) := by
      rintro _ ⟨_,⟨d,rfl⟩,rfl⟩
      obtain ⟨d',hd'⟩ := hu d
      exact ⟨d',hd'.symm⟩
    apply (Subgroup.eq_of_le_of_card_ge hle)
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
  obtain ⟨g,hg⟩ := BinaryNormalizer.exists_natural_actor ⟨u,hnorm⟩
  refine ⟨g,fun x => ?_⟩
  have he : mk F (a x) = mk F (traceZeroAction F g x) := by
    rw [←hb]
    exact hg (mk F x)
  rcases (binary_mk_eq_iff _ _).mp he with he | he
  · exact he
  · have hq := binary_form_normalized a.toLinearMap hai han x
    change form F (a x) = form F x at hq
    rw [he,binary_form_add_identity] at hq
    have hgq : form F (traceZeroAction F g x) = form F x := Atlas.SplitOctonion.automorphism_norm g x.val
    rw [hgq] at hq
    exact (one_ne_zero (add_left_cancel (hq.trans (add_zero _).symm))).elim

end
end Atlas.G2.Natural.OrthogonalCover
