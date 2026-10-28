module
public import Theory.Representation.SpecialLinearRestriction
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# A central cubic operator and a natural restriction over F₄

Evaluation at an operator satisfying x²+x+1=0 gives an actual action of the
quadratic field F₄ on the original binary vector space. A commuting group
action is field-linear. In binary dimension six the field dimension is three;
perfectness gives determinant one and hence an embedding in SL₃(F₄).

This isolates the reusable scalar construction behind Aschbacher--Smith
C.1.22, printed p.129. It follows the field construction in the checked
covered-six `FieldModel`, without needing any hexacode recognition theorem.
-/

@[expose] public noncomputable section
namespace Representation.CentralCubicRestriction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (z : G)
  (hz : z ∈ Subgroup.center G) (hq : ρ z ^ 2 + ρ z + 1 = 0)

/-- The actual quadratic field of four elements. -/
abbrev F := SL2FourNatural.F

/-- Evaluate the quadratic generator at the given central operator. -/
def scalarMap : F →ₐ[ZMod 2] Module.End (ZMod 2) V :=
  QuadraticAlgebra.lift ⟨ρ z, by
    have he : ρ z ^ 2 = -(ρ z + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using hq
    have hn (a : Module.End (ZMod 2) V) : -a = a := by
      rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

/-- The recovered scalars act on the original additive group. -/
@[instance_reducible] def fieldModule : Module F V :=
  Module.compHom _ (scalarMap ρ z hq).toRingHom

/-- The original binary scalar structure is preserved. -/
theorem fieldTower : letI := fieldModule ρ z hq
    IsScalarTower (ZMod 2) F V := by
  let := fieldModule ρ z hq
  constructor
  intro r a v
  change scalarMap ρ z hq (r • a) v = r • (scalarMap ρ z hq a v)
  rw [map_smul]
  rfl

/-- Every group operator is linear over the recovered field. -/
def fieldRepresentation : letI := fieldModule ρ z hq
    Representation F G V := by
  let := fieldModule ρ z hq
  refine { toFun := fun g => { (ρ g).toAddHom with map_smul' := ?_ }
           map_one' := ?_, map_mul' := ?_ }
  · intro a v
    have hc : ρ g (ρ z v) = ρ z (ρ g v) := by
      change (ρ g * ρ z) v = (ρ z * ρ g) v
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
    change ρ g (a.re • v + a.im • ρ z v) = a.re • ρ g v + a.im • ρ z (ρ g v)
    rw [map_add, map_smul, map_smul, hc]
  · apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ρ.map_one v
  · intro g j
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (ρ.map_mul g j) v

include hz hq in
/-- A faithful binary six-space is the restricted natural SL₃(F₄) module.
The module structure, coordinate equivalence, and intertwining are constructed. -/
theorem exists_natural_restriction [Finite V] [Group.IsPerfect G]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 6) :
    ∃ m : Module F V, letI := m
      IsScalarTower (ZMod 2) F V ∧
      ∃ (f : G →* Matrix.SpecialLinearGroup (Fin 3) F) (e : V ≃ₗ[F] (Fin 3 → F)),
        Function.Injective f ∧ ∀ g v, e (ρ g v) = specialLinearNatural 3 (f g) (e v) := by
  let := fieldModule ρ z hq
  let := fieldTower ρ z hq
  have hdim : Module.finrank F V = 3 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) F V
    rw [QuadraticAlgebra.finrank_eq_two, hd] at ht
    omega
  have hfaith : Function.Injective (fieldRepresentation ρ z hz hq) := by
    intro g j he
    apply hf
    ext v
    exact LinearMap.congr_fun he v
  obtain ⟨f, e, hfi, he⟩ := exists_specialLinear_restriction
    (fieldRepresentation ρ z hz hq) hfaith
    (det_eq_one_of_perfect _) hdim
  exact ⟨fieldModule ρ z hq, fieldTower ρ z hq, f, e, hfi, he⟩

end Representation.CentralCubicRestriction
