module

public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer
public import Theory.Representation.G2.NaturalInvolutionRank
public import Theory.Representation.G2NaturalTransitivity
public import Theory.LinearAlgebra.BinaryFourFixedSpace

/-!
# Hyperplanes in the binary natural G₂ module

A pointwise hyperplane fixer has square one over F₂. The actual G₂ involution
rank bound then forces it to be the identity. The invariant nondegenerate
alternating form identifies each hyperplane with a nonzero vector, so the
actual derived G₂ group acts transitively on hyperplanes.

These are the model inputs for the hyperplane step of Aschbacher--Smith
13.3.12(1), printed p.889. The natural action and its ATLAS attribution are
retained through the imported octonion model.
-/

public section
open Module Submodule LinearMap
namespace Atlas.G2.Natural.BinaryNondegeneratePlane

lemma pointwise_hyperplane_trivial (U : Submodule K W)
    (hU : finrank K U + 1 = finrank K W) (g : Model K)
    (hfix : ∀ v ∈ U, rho g v = v) : g = 1 := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)
  have he : ∀ v ∈ U, e v = v := hfix
  have hquot : finrank K (W ⧸ U) ≤ 1 := by
    have := U.finrank_quotient_add_finrank
    omega
  have hsq := BinaryFourFixedSpace.pointwiseFixer_sq U hquot ⟨e, he⟩
  have hg2 : g * g = 1 := by
    apply rho_injective
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun a : BinaryFourFixedSpace.pointwiseFixer U => a.val v) hsq
    change rho g (rho g v) = v at hh
    simpa only [map_mul, Module.End.mul_apply, map_one, Module.End.one_apply] using hh
  by_contra hne
  have hr := InvolutionRank.two_le_operatorFixedCodim_of_involution g hne hg2
  have heq := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    (Natural.action K g) (rho g) (Restricted.NaturalCoordinates.equiv K)
    (fun v => LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv K).isIntertwining' g) v)
  rw [heq] at hr
  have hker : U ≤ (rho g - 1).ker := by
    intro v hv
    change rho g v - v = 0
    exact sub_eq_zero.mpr (hfix v hv)
  have hd := Submodule.finrank_mono hker
  have hnull := (rho g - 1).finrank_range_add_finrank_ker
  change 2 ≤ finrank K (rho g - 1).range at hr
  change finrank K (rho g - 1).range + finrank K (rho g - 1).ker = finrank K W at hnull
  change finrank K U ≤ finrank K (rho g - 1).ker at hd
  omega

lemma hyperplane_eq_form_ker (U : Submodule K W)
    (hU : finrank K U + 1 = finrank K W) :
    ∃ v : W, v ≠ 0 ∧ U = (form v).ker := by
  have hdim : finrank K (form.orthogonal U) = 1 := by
    rw [form.finrank_orthogonal form_nondegenerate]
    omega
  let : Nontrivial (form.orthogonal U) := Module.nontrivial_of_finrank_pos (R := K) (M := form.orthogonal U) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : form.orthogonal U)
  have hv0 : (v : W) ≠ 0 := fun h => hv (Subtype.ext h)
  have hf : form v ≠ 0 := by
    intro hf
    exact hv0 (form_nondegenerate.1 v (by intro w; exact LinearMap.congr_fun hf w))
  have hle : U ≤ (form v).ker := by
    intro w hw
    exact form_alternating.isRefl _ _ (v.property w hw)
  refine ⟨v,hv0,Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

lemma derived_hyperplane_transitive (U U' : Submodule K W)
    (hU : finrank K U + 1 = finrank K W)
    (hU' : finrank K U' + 1 = finrank K W) :
    ∃ g : commutator (Model K), U.map (rho g.val) = U' := by
  obtain ⟨v,hv,rfl⟩ := hyperplane_eq_form_ker U hU
  obtain ⟨w,hw,rfl⟩ := hyperplane_eq_form_ker U' hU'
  let E := Restricted.NaturalCoordinates.equiv K
  obtain ⟨g,hg⟩ := derivedAction_transitive K (E.symm v) (E.symm w)
    (by simpa using hv) (by simpa using hw)
  have he : rho g.val v = w := by
    have hh := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv K).isIntertwining' g.val) (E.symm v)
    change E (derivedAction K g (E.symm v)) = rho g.val (E (E.symm v)) at hh
    simpa only [hg, E.apply_symm_apply] using hh.symm
  refine ⟨g, ?_⟩
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    change form w (rho g.val y) = 0
    rw [← he, form_invariant]
    exact hy
  · intro hz
    refine ⟨rho g.val⁻¹ z, ?_, ?_⟩
    · change form v (rho g.val⁻¹ z) = 0
      have hh := form_invariant g.val v (rho g.val⁻¹ z)
      rw [he, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at hh
      exact hh.symm.trans hz
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
end Atlas.G2.Natural.BinaryNondegeneratePlane
