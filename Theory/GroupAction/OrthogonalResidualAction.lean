module
public import Theory.SpecificGroups.OrthogonalFourBinary.ResidualNormalizer
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Cubic residual coordinates for an ambient conjugation action

Conjugation on an elementary four-space is marked by binary orthogonal
coordinates. A two-perfect subgroup normalizing the actual cubic residual
then commutes with its action. An equivariant whole-actor marking supplies
the image of the literal embedded two-residual. Finally, commuting actions
propagate centralization from a seed to its full orbit span.

Source application: Aschbacher--Smith 13.2.14, printed p.883. The statements
use relative normalizers throughout; ambient normality is not assumed.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace OrthogonalFourBinary.ResidualAction
open TerminalLines
variable {G : Type*} [Group G] (W : Subgroup G) [IsElementaryAbelian 2 W]

noncomputable def coordinateAction (c : Additive W ≃ₗ[F] Space) :
    normalizer (W : Set G) →* LinearActor where
  toFun a := c.symm.trans (((W.normalizerMonoidHom a).toAdditive.toLinearEquiv
    (fun t v => ZMod.map_smul (W.normalizerMonoidHom a).toAdditive.toAddMonoidHom t v)).trans c)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change c (Additive.ofMul (W.normalizerMonoidHom 1 (c.symm v).toMul)) = v
    rw [map_one]
    exact c.apply_symm_apply v
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    change c (Additive.ofMul (W.normalizerMonoidHom (a*b) (c.symm v).toMul)) =
      c (Additive.ofMul (W.normalizerMonoidHom a
        ((c.symm (c (Additive.ofMul (W.normalizerMonoidHom b (c.symm v).toMul))))).toMul))
    rw [c.symm_apply_apply,map_mul]
    rfl

@[simp] theorem coordinateAction_apply (c : Additive W ≃ₗ[F] Space)
    (a : normalizer (W : Set G)) (w : W) :
    coordinateAction W c a (c (Additive.ofMul w)) =
      c (Additive.ofMul (W.normalizerMonoidHom a w)) := by
  change c (Additive.ofMul (W.normalizerMonoidHom a
    (c.symm (c (Additive.ofMul w))).toMul)) = _
  rw [c.symm_apply_apply]
  rfl

theorem coordinateAction_eq_one_iff (c : Additive W ≃ₗ[F] Space)
    (a : normalizer (W : Set G)) :
    coordinateAction W c a = 1 ↔ (a : G) ∈ centralizer (W : Set G) := by
  constructor
  · intro he w hw
    have hh := congrArg (fun f : LinearActor => f (c (Additive.ofMul ⟨w,hw⟩))) he
    rw [coordinateAction_apply] at hh
    have hz := congrArg (fun v : Additive W => (v.toMul : G)) (c.injective hh)
    change (a:G)*w*(a:G)⁻¹ = w at hz
    exact (mul_inv_eq_iff_eq_mul.mp hz).symm
  · intro hc
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := c.surjective v
    change coordinateAction W c a (c (Additive.ofMul w.toMul)) = c (Additive.ofMul w.toMul)
    rw [coordinateAction_apply]
    apply congrArg c
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a:G)*(w.toMul:G)*(a:G)⁻¹ = w.toMul
    rw [← hc w.toMul w.toMul.property,mul_inv_cancel_right]

/-- The actual commutator of a two-perfect normalizer with the cubic residual
centralizes the original elementary four-space. -/
theorem commutator_centralizes_of_rotations
    (c : Additive W ≃ₗ[F] Space) (A R : Subgroup G)
    (hA : IsPPerfect 2 A) (hAW : A ≤ normalizer (W : Set G))
    (hRW : R ≤ normalizer (W : Set G)) (hAR : A ≤ normalizer (R : Set G))
    (himage : (R.subgroupOf (normalizer (W : Set G))).map (coordinateAction W c) =
      linearRotations) :
    ⁅A,R⁆ ≤ centralizer (W : Set G) := by
  let N := normalizer (W : Set G)
  let f := coordinateAction W c
  let a := f.comp (inclusion hAW)
  have hn : a.range ≤ normalizer (linearRotations : Set LinearActor) := by
    rintro _ ⟨x,rfl⟩
    rw [← himage]
    apply (R.subgroupOf N).le_normalizer_map f
    apply mem_map_of_mem f
    apply mem_normalizer_iff.mpr
    intro r
    change (r:G) ∈ R ↔ (x:G)*(r:G)*(x:G)⁻¹ ∈ R
    exact mem_normalizer_iff.mp (hAR x.property) r
  have hc := twoPerfect_linear_normalizer_centralizes_rotations hA a hn
  apply commutator_le.mpr
  intro x hx r hr
  let xN : N := ⟨x,hAW hx⟩
  let rN : N := ⟨r,hRW hr⟩
  have hcomm : Commute (f xN) (f rN) := by
    apply Commute.symm
    exact hc ⟨⟨x,hx⟩,rfl⟩ _ (himage ▸ mem_map_of_mem f (show rN ∈ R.subgroupOf N from hr))
  have he : f ⁅xN,rN⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq
  exact (coordinateAction_eq_one_iff W c ⁅xN,rN⁆).mp he

/-- An equivariant marking of the whole orthogonal actor identifies the image
of the literal embedded two-residual with the independent cubic rotations. -/
theorem embedded_residual_image [Finite G]
    (c : Additive W ≃ₗ[F] Space) (H : Subgroup G)
    (hHW : H ≤ normalizer (W : Set G))
    (q : H →* IsometryGroup) (hq : Function.Surjective q)
    (hc : ∀ (h : H) (w : W),
      coordinateAction W c ⟨h,hHW h.property⟩ (c (Additive.ofMul w)) =
        (q h).val (c (Additive.ofMul w))) :
    (((pResidual 2 H).map H.subtype).subgroupOf (normalizer (W : Set G))).map
      (coordinateAction W c) = linearRotations := by
  let f := coordinateAction W c
  have he (h : H) : f ⟨h,hHW h.property⟩ = (q h).val := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := c.surjective v
    exact hc h w.toMul
  have him : (pResidual 2 H).map q = rotations :=
    (map_pResidual_of_surjective 2 q hq).trans residual_eq_rotations
  apply le_antisymm
  · rintro _ ⟨a,⟨h,hh,ha⟩,rfl⟩
    have ha' : a = (⟨h,hHW h.property⟩ : normalizer (W : Set G)) := Subtype.ext ha.symm
    rw [ha',he]
    exact mem_map_of_mem IsometryGroup.subtype (him ▸ mem_map_of_mem q hh)
  · rintro _ ⟨r,hr,rfl⟩
    rw [← him] at hr
    obtain ⟨h,hh,rfl⟩ := hr
    exact ⟨⟨h,hHW h.property⟩,mem_map_of_mem H.subtype hh,he h⟩

end OrthogonalFourBinary.ResidualAction

namespace Subgroup
variable {G : Type*} [Group G]
/-- Commuting actions on an orbit span propagate centralization of its seed. -/
theorem centralizes_conjugateSpan_of_commutator_centralizes
    (A R Z : Subgroup G) (hAZ : A ≤ centralizer (Z : Set G))
    (hcomm : ⁅A,R⁆ ≤ centralizer (conjugateSpanBy Z R : Set G)) :
    A ≤ centralizer (conjugateSpanBy Z R : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨r,hr,z,hz,rfl⟩ a ha
  have hw : r*z*r⁻¹ ∈ conjugateSpanBy Z R := subset_closure ⟨r,hr,z,hz,rfl⟩
  have he := hcomm (commutator_mem_commutator ha hr) _ hw
  have hi : a⁻¹*z*a = z := by
    rw [← hAZ (A.inv_mem ha) z hz,inv_mul_cancel_right]
  have heq : a*(r*z*r⁻¹)*a⁻¹ = r*z*r⁻¹ := by
    calc
      _ = ⁅a,r⁆*(r*z*r⁻¹)*⁅a,r⁆⁻¹ := by
        simp only [commutatorElement_def]
        calc
          _ = a*r*(a⁻¹*z*a)*r⁻¹*a⁻¹ := by rw [hi]; group
          _ = _ := by group
      _ = r*z*r⁻¹ := mul_inv_eq_iff_eq_mul.mpr he.symm
  exact mul_inv_eq_iff_eq_mul.mp heq
end Subgroup
