module
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.Action
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

/-!
# Equal-norm reflection products in the ternary Omega group

Over F₃, reflection in a vector of norm q = ±1 is x ↦ x + q(a,x)a.
Two orthogonal vectors with the same nonzero norm are exchanged by reflection
in their difference. Their reflection product is therefore a literal
commutator of full isometries, which places it in the original Omega carrier.
This supplies the six generators of the triangle stabilizer's four-line actions.
Source: Aschbacher--Smith F.5.1--F.5.3, printed pp.300--301.
-/

@[expose] public section

namespace OmegaSixThree.TriangleLocal
open SixTernaryCoordinates OrthogonalityGraph

private theorem pairing_add_right (a x y : Space) :
    pairing a (x+y) = pairing a x + pairing a y := by
  simp only [pairing,Pi.add_apply]; ring
private theorem pairing_smul_right (a x : Space) (c : ZMod 3) :
    pairing a (c • x) = c * pairing a x := by
  rw [pairing_symm,pairing_smul_left,pairing_symm]
private theorem quadratic_smul (c : ZMod 3) (a : Space) :
    quadratic (c • a) = c^2 * quadratic a := by
  simp only [quadratic,Pi.smul_apply,smul_eq_mul]; ring

/-- Reflection in a norm-one or norm-minus-one vector, over the ternary field. -/
def reflect (q : ZMod 3) (a x : Space) : Space := x + (q * pairing a x) • a

theorem reflect_involutive (q : ZMod 3) (hq : q^2=1)
    (a : Space) (ha : quadratic a = q) : Function.Involutive (reflect q a) := by
  intro x
  ext i
  simp only [reflect,pairing_add_right,pairing_smul_right,pairing_self,ha,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have he : q^3 = q := by rw [pow_succ,hq,one_mul]
  ring_nf
  rw [he]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination q * pairing a x * a i * h3

private theorem reflect_norm (q : ZMod 3) (hq : q^2=1)
    (a : Space) (ha : quadratic a = q) (x : Space) :
    quadratic (reflect q a x) = quadratic x := by
  have h := polar_eq x ((q * pairing a x) • a)
  rw [quadratic_smul,ha,pairing_smul_right,pairing_symm x a] at h
  change quadratic (x + (q * pairing a x) • a) = _
  have he : q^3 = q := by rw [pow_succ,hq,one_mul]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination h + pairing a x ^ 2 * he + q * pairing a x ^ 2 * h3

def reflection (q : ZMod 3) (hq : q^2=1) (a : Space) (ha : quadratic a = q) : LinearGroup where
  toFun := reflect q a
  invFun := reflect q a
  left_inv := reflect_involutive q hq a ha
  right_inv := reflect_involutive q hq a ha
  map_add' x y := by
    simp only [reflect,pairing_add_right,mul_add,add_smul]
    abel
  map_smul' c x := by
    simp only [reflect,pairing_smul_right,smul_add,smul_smul,RingHom.id_apply]
    congr 1
    ring

theorem reflection_mem (q : ZMod 3) (hq : q^2=1) (a : Space) (ha : quadratic a = q) :
    reflection q hq a ha ∈ orthogonalGroup := reflect_norm q hq a ha

theorem reflection_conjugate (q : ZMod 3) (hq : q^2=1) (a : Space)
    (ha : quadratic a = q) (g : orthogonalGroup) :
    g.val * reflection q hq a ha * g.val⁻¹ =
      reflection q hq (g.val a) ((g.property a).trans ha) := by
  apply LinearEquiv.ext
  intro x
  change g.val (reflect q a (g.val.symm x)) = reflect q (g.val a) x
  simp only [reflect,map_add,map_smul,g.val.apply_symm_apply]
  congr 2
  have hh := pairing_orthogonal g a (g.val.symm x)
  simpa only [g.val.apply_symm_apply] using congrArg (q * ·) hh.symm

private theorem quadratic_sub (a b : Space) :
    quadratic (a-b) = quadratic a + quadratic b - 2*pairing a b := by
  simp only [quadratic,pairing,Pi.sub_apply]
  ring

/-- Products of reflections in two orthogonal vectors of equal norm are
literal commutators, hence belong to the displayed Omega subgroup. -/
theorem reflection_pair_mem (q : ZMod 3) (hq : q^2=1) (a b : Space)
    (ha : quadratic a = q) (hb : quadratic b = q) (hab : pairing a b = 0) :
    reflection q hq a ha * reflection q hq b hb ∈ omegaPlusSixThree := by
  have hd : quadratic (a-b) = -q := by
    rw [quadratic_sub,ha,hb,hab,mul_zero,sub_zero]
    have h3 : (3 : ZMod 3)=0 := by decide
    linear_combination q * h3
  let t := reflection (-q) (by simpa using hq) (a-b) hd
  have ht : t ∈ orthogonalGroup := reflection_mem _ _ _ _
  have hta : t a = b := by
    change a + ((-q) * pairing (a-b) a) • (a-b) = b
    have hp : pairing (a-b) a = q := by
      simp only [pairing,Pi.sub_apply] at *
      have hs := pairing_symm a b
      change _ = _ at hs
      simp only [pairing] at hs
      rw [←ha]
      simp only [quadratic]
      linear_combination -hab
    rw [hp]
    have he : (-q)*q = -1 := by rw [neg_mul,←pow_two,hq]
    rw [he,neg_one_smul]
    abel
  have hc := reflection_conjugate q hq a ha ⟨t,ht⟩
  have hc' : t * reflection q hq a ha * t⁻¹ = reflection q hq b hb := by
    simpa only [hta] using hc
  have he : commutatorWord (reflection q hq a ha) t =
      reflection q hq a ha * reflection q hq b hb := by
    change reflection q hq a ha * t * reflection q hq a ha * t⁻¹ = _
    simpa only [mul_assoc] using congrArg (fun r => reflection q hq a ha * r) hc'
  rw [←he]
  exact commutatorWord_mem_omegaPlusSixThree (reflection_mem _ _ _ _) ht

end OmegaSixThree.TriangleLocal
