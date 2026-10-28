module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.Cocycles
import Mathlib.Tactic.Group

/-!
# An actual non-inner adjustment of the marked hexad extension

The quadratic cocycle acts on the original group itself. Its construction
requires only the original quotient and exact conjugation coordinates on the
whole kernel; it does not require a complement or an affine model. The
resulting involutory automorphism fixes that kernel pointwise and induces the
identity on the literal A₆ quotient.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Subgroup

/-- The nonprincipal quadratic displacement gives an actual involutory
kernel-fixing automorphism of any extension with the marked polar action.
It cannot be induced by conjugating with a kernel element. -/
theorem exists_original_quadratic_automorphism {D : Type*} [Group D]
    (q : D →* A6) (hq : Function.Surjective q)
    (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd)) :
    ∃ α : MulAut D,
      (∀ g, q (α g) = q g) ∧
      (∀ a : q.ker, α a = (a : D)) ∧
      (∀ g, α g = (k.symm (Multiplicative.ofAdd (quadratic (q g))) : D) * g) ∧
      (∀ g, α (α g) = g) ∧
      ¬ ∃ a : q.ker, ∀ g, α g = (a : D)⁻¹ * g * a := by
  let j : NaturalModule → D := fun v => k.symm (Multiplicative.ofAdd v)
  have hj0 : j 0 = 1 := by simp [j]
  have hjadd (v w : NaturalModule) : j (v+w) = j v * j w := by
    change ((k.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : q.ker) : D) = _
    rw [map_mul]
    rfl
  have hjq (v : NaturalModule) : q (j v) = 1 := (k.symm (Multiplicative.ofAdd v)).property
  have hji : Function.Injective j := fun v w h =>
    Multiplicative.ofAdd.injective (k.symm.injective (Subtype.ext h))
  have hjconj (g : D) (v : NaturalModule) :
      j (polarAction (q g).val v) = g * j v * g⁻¹ := by
    have hh := congrArg (fun x : Multiplicative NaturalModule => (k.symm x : D))
      (hk g (k.symm (Multiplicative.ofAdd v)))
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      toAdd_ofAdd, MulAut.conjNormal_apply, j] using hh.symm
  have hjself (v : NaturalModule) : j v * j v = 1 := by
    rw [←hjadd]
    have hh : v+v=0 := by ext i; exact CharTwo.add_self_eq_zero _
    rw [hh,hj0]
  let f : D → D := fun g => j (quadratic (q g)) * g
  have hfq (g : D) : q (f g) = q g := by
    simp only [f,map_mul,hjq,one_mul]
  have hfmul (g h : D) : f (g*h) = f g * f h := by
    dsimp only [f]
    rw [map_mul,quadratic_mul,add_comm (polarAction _ _) (quadratic _),hjadd,hjconj]
    group
  have hff (g : D) : f (f g) = g := by
    change j (quadratic (q (f g))) * (j (quadratic (q g)) * g) = g
    rw [hfq,←mul_assoc,hjself,one_mul]
  let α : MulAut D :=
    { toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      map_mul' := hfmul }
  refine ⟨α,hfq,?_,fun _ => rfl,hff,?_⟩
  · intro a
    change j (quadratic (q a)) * a = (a : D)
    rw [a.property,quadratic_one,hj0,one_mul]
  · rintro ⟨a,ha⟩
    apply quadratic_not_principal
    let v : NaturalModule := (k a).toAdd
    have hva : j v = (a : D) := congrArg Subtype.val (k.symm_apply_apply a)
    refine ⟨v,fun x => ?_⟩
    obtain ⟨g,rfl⟩ := hq x
    apply hji
    have he := ha g
    change j (quadratic (q g)) * g = (a : D)⁻¹ * g * a at he
    have hneg : polarAction (q g).val v - v = v + polarAction (q g).val v := by
      ext i
      simp only [Pi.sub_apply,Pi.add_apply,CharTwo.sub_eq_add,add_comm]
    rw [hneg,hjadd,hjconj,hva]
    have ha2 : (a : D) * a = 1 := hva ▸ hjself v
    have hai : (a : D)⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
    rw [hai] at he
    calc
      j (quadratic (q g)) = ((a : D)*g*a)*g⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
      _ = (a : D) * (g * a * g⁻¹) := by group

end Theory.SpecificGroups.SymmetricSix.PolarAffine
