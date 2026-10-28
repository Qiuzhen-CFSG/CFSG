module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Complement
public import Theory.LinearAlgebra.QuadraticForm.BinaryAnisotropic
/-!
# A cubic actor on each orthogonal complement

A four-dimensional complement to the polar radical of the five-dimensional
orthogonal cover has nondegenerate polar form. The binary anisotropic bound
provides a singular vector, hence a hyperbolic pair. Scaling that pair by
inverse units and fixing its perpendicular space embeds the field's unit
group in the complement stabilizer. Over F₄ this gives an element of order
three moving a vector of the complement.

The odd-orthogonal projection is compared pointwise with the original full
cover action, so the resulting matrix acts on the same complement. The
original-hyperplane application is in OriginalCubic. Final source assembly
belongs to qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, 11.2.2, printed p.767.
-/

open Module ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal.TheoremDRootNormalizer
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalCubic
variable {F : Type*} [Field F]

theorem hyperbolic_pair [Finite F] [CharP F 2] [Algebra (ZMod 2) F] (Q : Submodule F (Space (K := F)))
    (hQ : IsCompl Q radical) (hd : Module.finrank F Q = 4) :
    ∃ e f : Q, formB 2 F e.val = 0 ∧ formB 2 F f.val = 0 ∧
      (formB 2 F).polarBilin e.val f.val = 1 := by
  let q := (formB 2 F).comp Q.subtype
  have hnd : q.polarBilin.Nondegenerate :=
    OrthogonalComplements.complement_polar_nondegenerate Q hQ
  have hna : ¬ q.Anisotropic := by
    intro ha
    let : Finite Q := Module.finite_of_finite F
    have hh := (q.restrictScalars (S := ZMod 2)).finrank_le_twice_of_anisotropic_binary ha
    have ht := Module.finrank_mul_finrank (ZMod 2) F Q
    rw [hd] at ht
    have hpos : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
    omega
  obtain ⟨e,he,he0⟩ : ∃ e : Q, q e = 0 ∧ e ≠ 0 := by
    have hh : ¬ ∀ e : Q, q e = 0 → e = 0 := hna
    push Not at hh
    exact hh
  obtain ⟨f,hf⟩ := exists_normalized_partner q e (fun hz => he0 (hnd.1 e hz))
  exact ⟨e,f-q f • e,he,(partner_correction q e f he hf).1,
    (partner_correction q e f he hf).2⟩

/-- The existing odd-orthogonal projection has exactly the covering action. -/
theorem fullAction_evenProjection [Finite F] [CharP F 2]
    (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F))
    (x : Space (K := F)) : fullAction (evenProjection g) x = g.val x := by
  have hfst : (fullAction (evenProjection g) x).1 = (g.val x).1 := by
    change (evenProjection g • x.1) = _
    rw [evenProjection_apply, even_first g x]
  apply Prod.ext hfst
  apply CharTwo.sq_injective
  have h1 := fullAction_preserves (evenProjection g) x
  have h2 := ReflectionGeneration.isometry_preserves _ g x
  rw [formB_apply, hfst] at h1
  rw [formB_apply] at h2
  exact add_left_cancel (h1.trans h2.symm)

variable (e f : Space (K := F)) (he : formB 2 F e = 0)
  (hf : formB 2 F f = 0) (hef : (formB 2 F).polarBilin e f = 1)

private def torusLinear (u : Fˣ) : Space (K := F) ≃ₗ[F] Space (K := F) :=
  let s := split (formB 2 F) e f he hf hef
  (s.trans (((LinearEquiv.smulOfUnit u).prodCongr (LinearEquiv.smulOfUnit u⁻¹)).prodCongr
    (LinearEquiv.refl F _))).trans s.symm

private theorem torusLinear_preserves (u : Fˣ) (x : Space (K := F)) :
    formB 2 F (torusLinear e f he hf hef u x) = formB 2 F x := by
  change formB 2 F ((split (formB 2 F) e f he hf hef).symm
    (((u : F) * (split (formB 2 F) e f he hf hef x).1.1,
      (↑u⁻¹ : F) * (split (formB 2 F) e f he hf hef x).1.2),
      (split (formB 2 F) e f he hf hef x).2)) = _
  rw [split_form, form_split (formB 2 F) e f he hf hef x]
  congr 1
  calc
    _ = ((u : F) * ↑u⁻¹) * ((split (formB 2 F) e f he hf hef x).1.1 *
      (split (formB 2 F) e f he hf hef x).1.2) := by ring
    _ = _ := by rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_mul]

private def torus : Fˣ →* Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F) where
  toFun u := ⟨torusLinear e f he hf hef u,
    (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
      (torusLinear_preserves e f he hf hef u)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change torusLinear e f he hf hef 1 x = x
    simp [torusLinear, LinearEquiv.smulOfUnit]
  map_mul' u v := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change torusLinear e f he hf hef (u * v) x =
      torusLinear e f he hf hef u (torusLinear e f he hf hef v x)
    apply (split (formB 2 F) e f he hf hef).injective
    simp [torusLinear, LinearEquiv.smulOfUnit, mul_comm, mul_smul]

private theorem torus_apply_e (u : Fˣ) : (torus e f he hf hef u).val e = (u : F) • e := by
  change torusLinear e f he hf hef u e = _
  simp only [torusLinear, LinearEquiv.trans_apply, split_e, LinearEquiv.prodCongr_apply]
  simpa only [Units.smul_def] using (by simp [LinearEquiv.smulOfUnit, split] :
    (split (formB 2 F) e f he hf hef).symm
      (((LinearEquiv.smulOfUnit u) 1, (LinearEquiv.smulOfUnit u⁻¹) 0),
        (LinearEquiv.refl F _) 0) = u • e)

private theorem torus_mem (u : Fˣ) (Q : Submodule F (Space (K := F)))
    (heQ : e ∈ Q) (hfQ : f ∈ Q) {x : Space (K := F)} (hx : x ∈ Q) :
    (torus e f he hf hef u).val x ∈ Q := by
  change ((u : F) * (formB 2 F).polarBilin x f) • e +
    ((↑u⁻¹ : F) * (formB 2 F).polarBilin x e) • f +
      (x - ((formB 2 F).polarBilin x f • e + (formB 2 F).polarBilin x e • f)) ∈ Q
  exact Q.add_mem (Q.add_mem (Q.smul_mem _ heQ) (Q.smul_mem _ hfQ))
    (Q.sub_mem hx (Q.add_mem (Q.smul_mem _ heQ) (Q.smul_mem _ hfQ)))

private theorem torus_stabilizes (u : Fˣ) (Q : Submodule F (Space (K := F)))
    (heQ : e ∈ Q) (hfQ : f ∈ Q) :
    Q.map (torus e f he hf hef u).val.toLinearMap = Q := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x,hx,rfl⟩
    exact torus_mem e f he hf hef u Q heQ hfQ hx
  · exact LinearEquiv.finrank_map_eq (torus e f he hf hef u).val Q

theorem exists_cubic [Finite F] [CharP F 2] [Algebra (ZMod 2) F] (hcard : Nat.card F = 4)
    (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical)
    (hd : Module.finrank F Q = 4) :
    ∃ g : Matrix.symplecticGroup (Fin 2) F, orderOf g = 3 ∧
      Q.map (fullAction g) = Q ∧ ∃ x ∈ Q, fullAction g x ≠ x := by
  obtain ⟨e,f,he,hf,hef⟩ := hyperbolic_pair Q hQ hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3
    (by rw [Nat.card_units,hcard])
  let t := torus e.val f.val he hf hef
  have ht : Function.Injective t := by
    intro u v huv
    have he0 : e.val ≠ 0 := by
      intro hz
      rw [hz, map_zero, LinearMap.zero_apply] at hef
      exact zero_ne_one hef
    have hh := congrArg (fun a => a.val e.val) huv
    rw [torus_apply_e,torus_apply_e] at hh
    exact Units.ext ((smul_left_injective F he0) hh)
  let g := evenProjection (t u)
  have hgo : orderOf g = 3 :=
    (orderOf_injective evenProjection evenProjection_injective (t u)).trans
      ((orderOf_injective t ht u).trans hu)
  refine ⟨g,hgo,?_,e.val,e.property,?_⟩
  · have hm := torus_stabilizes e.val f.val he hf hef u Q e.property f.property
    have ha : fullAction g = (t u).val.toLinearMap :=
      LinearMap.ext (fullAction_evenProjection (t u))
    rw [ha]
    exact hm
  · rw [fullAction_evenProjection,torus_apply_e]
    intro hh
    have he0 : e.val ≠ 0 := by
      intro hz
      rw [hz, map_zero, LinearMap.zero_apply] at hef
      exact zero_ne_one hef
    have hu1 : u = 1 := Units.ext ((smul_left_injective F he0)
      (hh.trans (one_smul F e.val).symm))
    simp only [hu1,orderOf_one] at hu
    omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalCubic
