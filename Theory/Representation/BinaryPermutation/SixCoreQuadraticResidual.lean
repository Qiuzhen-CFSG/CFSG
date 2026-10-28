module
public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement

/-!
# Mixed quadratic displacements in the six-letter core

In the five-dimensional binary augmentation core, a nonidentity element
of the literal cubic residual of a nonconstant-vector stabilizer has a
nonzero second displacement with one of its residual conjugates. For the
marked pair, two complementary 3-cycles detect every nonidentity A₄ actor.
Even-permutation transport and complementation handle every nonconstant
vector. Only the small four-letter and six-letter identities are computed.

The application in Aschbacher–Smith 13.4.8, printed p.904, rules out a
noncentral abelian residual subgroup normalized by both the residual and
the full five-space. It retains the augmentation core, not its natural
four-dimensional quotient.
-/

open Subgroup Theory.GroupTheory
namespace BinaryPermutation.SixCoreQuadraticResidual
open SixCoreResidualMovement
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype W := Subtype.fintype _
private def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private def a : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 4,by decide⟩
private def b : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 5,by decide⟩
private theorem a_stab : a ∈ S pair := by change rho a pair = pair; decide
private theorem b_stab : b ∈ S pair := by change rho b pair = pair; decide
private theorem a_res : (⟨a,a_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
  mem_primeToResidual_of_pow (n := 1) (by decide)
private theorem b_res : (⟨b,b_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
  mem_primeToResidual_of_pow (n := 1) (by decide)
open Theory.SpecificGroups.SymmetricSix
private theorem pair_stabilizer : S pair = a6DuadStabilizer := by
  ext g
  change rho g pair = pair ↔ g.val ∈ duadStabilizer
  revert g
  decide +kernel
private noncomputable def e : Equiv.Perm (Fin 4) ≃* S pair :=
  a6DuadModelEquiv.trans (MulEquiv.subgroupCongr pair_stabilizer.symm)
private theorem residual_sign (g : S pair) (hg : g ∈ primeToResidual 3 (S pair)) :
    signPermTwo (e.symm g) = 1 := by
  exact primeToResidual_le_ker (p := 3) (signPermTwo.comp e.symm.toMonoidHom)
    (by rw [Nat.card_eq_fintype_card]; decide) hg
private theorem pair_detection (g : Equiv.Perm (Fin 4))
    (hg : signPermTwo g = 1)
    (ha : ∀ v : W, rho (e g).val (rho (MulAut.conj a (e g).val) v - v) =
      rho (MulAut.conj a (e g).val) v - v)
    (hb : ∀ v : W, rho (e g).val (rho (MulAut.conj b (e g).val) v - v) =
      rho (MulAut.conj b (e g).val) v - v) : g = 1 := by
  revert g
  decide +kernel

private theorem pair_eq_one (x : S pair) (hx : x ∈ primeToResidual 3 (S pair))
    (hq : ∀ y : S pair, y ∈ primeToResidual 3 (S pair) → ∀ v : W,
      rho x.val (rho (MulAut.conj y.val x.val) v - v) =
        rho (MulAut.conj y.val x.val) v - v) : x = 1 := by
  have h := pair_detection (e.symm x) (residual_sign x hx)
    (by simpa only [MulEquiv.apply_symm_apply] using hq ⟨a,a_stab⟩ a_res)
    (by simpa only [MulEquiv.apply_symm_apply] using hq ⟨b,b_stab⟩ b_res)
  exact e.symm.injective (h.trans (map_one e.symm).symm)
private local instance : MulAction A W where
  smul g w := rho g w
  one_smul w := by change rho 1 w = w; rw [map_one]; rfl
  mul_smul g h w := by change rho (g*h) w = rho g (rho h w); rw [map_mul]; rfl
private theorem conjugate_action (g x : A) (v : W) :
    rho (MulAut.conj g x) (rho g v) = rho g (rho x v) := by
  change rho (g*x*g⁻¹) (rho g v) = _
  rw [← Module.End.mul_apply,← map_mul]
  simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]
private theorem rho_injective (g : A) : Function.Injective (rho g) := by
  intro v w h
  have hh := congrArg (rho g⁻¹) h
  simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
    Module.End.one_apply] using hh
private theorem conj_conj (g y x : A) :
    MulAut.conj (MulAut.conj g y) (MulAut.conj g x) =
      MulAut.conj g (MulAut.conj y x) := by
  simp only [MulAut.conj_apply]
  group

/-- No nonidentity residual actor has zero mixed displacement with all its
residual conjugates on the original five-dimensional augmentation core. -/
public theorem eq_one_of_conjugate_quadratic (w : W)
    (hw : ¬ ∀ g : A, rho g w = w)
    (x : S w) (hx : x ∈ primeToResidual 3 (S w))
    (hq : ∀ y : S w, y ∈ primeToResidual 3 (S w) → ∀ v : W,
      rho x.val (rho (MulAut.conj y.val x.val) v - v) =
        rho (MulAut.conj y.val x.val) v - v) : x = 1 := by
  classical
  have hw' := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  have step (w₀ : W) (hs : S w₀ = S pair) (g : A) (hg : rho g w₀ = w) : x = 1 := by
    have he : (S w₀).map (MulAut.conj g).toMonoidHom = S w := by
      rw [← hg]
      exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w₀).symm
    let f : S pair ≃* S w := (MulEquiv.subgroupCongr hs.symm).trans
      (((S w₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he))
    have hf (y : S pair) : (f y).val = MulAut.conj g y.val := rfl
    let x₀ := f.symm x
    have hx₀ : x₀ ∈ primeToResidual 3 (S pair) := by
      have hh := mem_map_of_mem f.symm.toMonoidHom hx
      rwa [map_primeToResidual f.symm] at hh
    have hxval : x.val = MulAut.conj g x₀.val := by
      rw [← hf,MulEquiv.apply_symm_apply]
    have hxone : x₀ = 1 := pair_eq_one x₀ hx₀ (by
      intro y hy v
      have hfy : f y ∈ primeToResidual 3 (S w) := by
        rw [← map_primeToResidual f]
        exact mem_map_of_mem f.toMonoidHom hy
      have hh := hq (f y) hfy (rho g v)
      rw [hf,hxval,conj_conj,conjugate_action,← map_sub,conjugate_action] at hh
      exact rho_injective g hh)
    exact f.symm.injective (hxone.trans (map_one f.symm).symm)
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hw'.1 hw'.2 with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · apply step (pair+sixCoreConstant) ?_ g hg
    ext y
    change rho y (pair+sixCoreConstant) = pair+sixCoreConstant ↔ rho y pair = pair
    rw [map_add,sixCoreConstant_fixed,add_left_inj]

end BinaryPermutation.SixCoreQuadraticResidual
