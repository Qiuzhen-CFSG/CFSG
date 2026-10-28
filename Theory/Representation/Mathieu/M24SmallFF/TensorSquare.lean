module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Exterior

/-!
# A binary tensor-square obstruction

An equivariant bilinear map with no exterior-square maps is symmetric.
Its diagonal is then linear over the two-element field. If the original
module also has no maps to the target, this diagonal vanishes, and a second
application of the exterior-square obstruction kills the bilinear map.

This supplies the two square-tensor steps in the native M24 FF argument.
-/

open Representation
open scoped TensorProduct
namespace Representation.Mathieu.M24SmallFF
open Representation.MathieuM24Degree44.FiveSpace
@[expose] public noncomputable section
variable {G U V : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
  (τ : Representation (ZMod 2) G U) (ρ : Representation (ZMod 2) G V)
private def altMap (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V) (hb : ∀u,b u u=0) :
    U [⋀^Fin 2]→ₗ[ZMod 2] V where
  toFun v := b (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp [map_add]
  map_update_smul' v i c x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 = v 1 at h
      change b (v 0) (v 1) = 0
      rw [h,hb]
    · change v 1 = v 0 at h
      change b (v 0) (v 1) = 0
      rw [h,hb]
    · exact (hij rfl).elim
private def exteriorMap (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V) (hb : ∀u,b u u=0)
    (he : ∀g u v,b (τ g u) (τ g v)=ρ g (b u v)) :
    (exteriorSquare τ).IntertwiningMap ρ where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (altMap b hb)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (exteriorPower.alternatingMapLinearEquiv (altMap b hb))
      (exteriorPower.map 2 (τ g) (exteriorPower.ιMulti (ZMod 2) 2 v)) = _
    rw [exteriorPower.map_apply_ιMulti]
    change (exteriorPower.alternatingMapLinearEquiv (altMap b hb))
      (exteriorPower.ιMulti (ZMod 2) 2 (τ g ∘ v)) =
      ρ g ((exteriorPower.alternatingMapLinearEquiv (altMap b hb))
        (exteriorPower.ιMulti (ZMod 2) 2 v))
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact he g (v 0) (v 1)
private lemma bilinear_zero_of_alternating
    (hz : ∀f:(exteriorSquare τ).IntertwiningMap ρ,f=0)
    (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V) (hb : ∀u,b u u=0)
    (he : ∀g u v,b (τ g u) (τ g v)=ρ g (b u v)) (u v : U) : b u v=0 := by
  have hh := congrArg (fun f : (exteriorSquare τ).IntertwiningMap ρ =>
    f (exteriorPower.ιMulti (ZMod 2) 2 ![u,v])) (hz (exteriorMap τ ρ b hb he))
  change (exteriorPower.alternatingMapLinearEquiv (altMap b hb))
    (exteriorPower.ιMulti (ZMod 2) 2 ![u,v]) = 0 at hh
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at hh
  exact hh
private lemma binary_add_self (v : V) : v+v=0 := by
  have hc : (1+1 : ZMod 2) = 0 := by decide
  have h := congrArg (fun c : ZMod 2 => c • v) hc
  simpa only [add_smul, one_smul, zero_smul] using h
private lemma binary_neg (v : V) : -v=v :=
  (eq_neg_of_add_eq_zero_left (binary_add_self v)).symm
lemma tensorSquare_map_zero
    (hz : ∀f:τ.IntertwiningMap ρ,f=0)
    (hext : ∀f:(exteriorSquare τ).IntertwiningMap ρ,f=0)
    (f : (τ.tprod τ).IntertwiningMap ρ) : f=0 := by
  let b := _root_.TensorProduct.curry f.toLinearMap
  have he (g:G) (u v:U) : b (τ g u) (τ g v)=ρ g (b u v) := by
    exact LinearMap.congr_fun (f.isIntertwining' g) (u ⊗ₜ[ZMod 2] v)
  have hsym (u v:U) : b u v = b v u := by
    have h := bilinear_zero_of_alternating τ ρ hext (b+b.flip)
      (fun u => by
        change b u u+b u u=0
        exact binary_add_self _) (fun g u v => by
          change b (τ g u) (τ g v)+b (τ g v) (τ g u)=ρ g (b u v+b v u)
          rw [he,he,map_add]) u v
    change b u v+b v u=0 at h
    exact (eq_neg_of_add_eq_zero_left h).trans (binary_neg _)
  let d : τ.IntertwiningMap ρ :=
    ⟨{toFun := fun u => b u u
      map_add' := by
        intro u v
        simp only [map_add, LinearMap.add_apply]
        rw [hsym v u]
        have h : b u v+b u v=0 := binary_add_self _
        calc
          b u u + b u v + (b u v + b v v) = b u u + (b u v + b u v) + b v v := by abel
          _ = b u u + b v v := by rw [h, add_zero]
      map_smul' := by
        intro c u
        have hc : c=0 ∨ c=1 := by revert c; decide
        rcases hc with rfl | rfl <;> simp}, by
      intro g
      apply LinearMap.ext
      intro u
      exact he g u u⟩
  have hdiag (u:U) : b u u=0 := congrArg (fun e:τ.IntertwiningMap ρ =>e u) (hz d)
  have hh := bilinear_zero_of_alternating τ ρ hext b hdiag he
  apply IntertwiningMap.ext
  apply _root_.TensorProduct.ext
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  exact hh u v
end
end Representation.Mathieu.M24SmallFF
