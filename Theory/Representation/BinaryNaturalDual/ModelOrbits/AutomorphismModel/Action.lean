module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Theory.Representation.BinaryNaturalDual.Action

/-!
# Constructing the full automorphism action on the natural-plus-dual module

Every automorphism has a unique expression as an inner automorphism or inverse
transpose followed by an inner automorphism. Assign the natural-plus-dual action
to the inner part and coordinate exchange to inverse transpose. The dot-product
identity proves covariance; together with the square-one identity this proves
the multiplication law in all four cases. Thus `coordinateAction` constructs the
specified representation of the actual automorphism group without any action
existence premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9 setup and
H.9.1, printed pp.389–390. This is the concrete module used by those statements.
-/

public section

open BinaryLinear BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.ModelOrbits.AutomorphismModel
variable {n : ℕ}

/-- Ordinary inverse transpose is involutive on the linear group. -/
theorem graph_involutive (n : ℕ) : Function.Involutive (graphLinear n) := by
  intro g
  exact MulEquiv.congr_fun (graphLinear_sq n) g

/-- The dot-product identification turns inverse transpose into the dual action. -/
theorem graph_dotProductEquiv (g : LinearGroup n) (x : OuterCyclic.Space n) :
    dotProductEquiv (ZMod 2) (Fin n) (graphLinear n g x) =
      g.symm.dualMap (dotProductEquiv (ZMod 2) (Fin n) x) := by
  apply LinearMap.ext
  intro y
  exact (by simpa using graphLinear_dotProduct g x (g.symm y))

/-- Covariance of coordinate exchange with the natural-plus-dual action. -/
theorem action_swap (g : LinearGroup n) :
    NaturalDualFlag.action g * coordinateSwap n =
      coordinateSwap n * NaturalDualFlag.action (graphLinear n g) := by
  apply LinearEquiv.ext
  intro v
  change naturalDualRepresentation g (coordinateSwap n v) =
    coordinateSwap n (naturalDualRepresentation (graphLinear n g) v)
  simp only [naturalDualRepresentation_apply, coordinateSwap_apply]
  apply Prod.ext
  · change g ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2) =
      (dotProductEquiv (ZMod 2) (Fin n)).symm
        ((graphLinear n g).symm.dualMap v.2)
    apply (dotProductEquiv (ZMod 2) (Fin n)).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := graph_dotProductEquiv (graphLinear n g)
      ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2)
    simpa only [graph_involutive n g, LinearEquiv.apply_symm_apply] using h
  · exact (graph_dotProductEquiv g v.1).symm

/-- Coordinate exchange has square one in the linear automorphism group. -/
theorem swap_sq (n : ℕ) : coordinateSwap n * coordinateSwap n = 1 := by
  apply LinearEquiv.ext
  exact coordinateSwap_involutive n

private noncomputable def normalForm (n : ℕ) (p : Bool × LinearGroup n) : MulAut (LinearGroup n) :=
  if p.1 then graphLinear n * MulAut.conj p.2 else MulAut.conj p.2

private theorem normalForm_bijective (hn : n = 4 ∨ n = 5) :
    Function.Bijective (normalForm n) := by
  constructor
  · rintro ⟨b, g⟩ ⟨c, h⟩ he
    have hi := MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by omega : 0 < n))
    have hne (a : LinearGroup n) : graphLinear n * MulAut.conj a ∉
        MulAut.innerSubgroup (LinearGroup n) := by
      intro ha
      apply graph_not_inner hn
      have hm := (MulAut.innerSubgroup (LinearGroup n)).mul_mem ha
        ((MulAut.innerSubgroup (LinearGroup n)).inv_mem ⟨a, rfl⟩)
      simpa only [mul_inv_cancel_right] using hm
    cases b <;> cases c <;> simp only [normalForm, Bool.false_eq_true, ↓reduceIte] at he
    · exact Prod.ext rfl (hi he)
    · exact (hne h (he ▸ (show MulAut.conj g ∈ MulAut.innerSubgroup (LinearGroup n)
        from ⟨g, rfl⟩))).elim
    · exact (hne g (he.symm ▸ (show MulAut.conj h ∈ MulAut.innerSubgroup (LinearGroup n)
        from ⟨h, rfl⟩))).elim
    · exact Prod.ext rfl (hi (mul_left_cancel he))
  · intro a
    obtain ⟨g, rfl | rfl⟩ := inner_graph hn a
    · exact ⟨(false, g), rfl⟩
    · exact ⟨(true, g), rfl⟩

private noncomputable def normalFormEquiv (hn : n = 4 ∨ n = 5) :
    Bool × LinearGroup n ≃ MulAut (LinearGroup n) :=
  Equiv.ofBijective (normalForm n) (normalForm_bijective hn)

private noncomputable def operator (hn : n = 4 ∨ n = 5)
    (a : MulAut (LinearGroup n)) : CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n :=
  let p := (normalFormEquiv hn).symm a
  if p.1 then coordinateSwap n * NaturalDualFlag.action p.2 else NaturalDualFlag.action p.2

private theorem operator_inner (hn : n = 4 ∨ n = 5) (g : LinearGroup n) :
    operator hn (MulAut.conj g) = NaturalDualFlag.action g := by
  have he : MulAut.conj g = normalFormEquiv hn (false, g) := rfl
  simp only [operator, he, Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]

private theorem operator_graph_inner (hn : n = 4 ∨ n = 5) (g : LinearGroup n) :
    operator hn (graphLinear n * MulAut.conj g) = coordinateSwap n * NaturalDualFlag.action g := by
  have he : graphLinear n * MulAut.conj g = normalFormEquiv hn (true, g) := rfl
  simp only [operator, he, Equiv.symm_apply_apply, ↓reduceIte]

private theorem inner_graph_comm (g : LinearGroup n) :
    MulAut.conj g * graphLinear n = graphLinear n * MulAut.conj (graphLinear n g) := by
  apply MulEquiv.ext
  intro h
  change g * graphLinear n h * g⁻¹ =
    graphLinear n (graphLinear n g * h * (graphLinear n g)⁻¹)
  simp only [map_mul, map_inv, graph_involutive n g]

private theorem operator_mul (hn : n = 4 ∨ n = 5)
    (a b : MulAut (LinearGroup n)) : operator hn (a * b) = operator hn a * operator hn b := by
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn a <;>
    obtain ⟨h, rfl | rfl⟩ := inner_graph hn b
  · rw [← map_mul, operator_inner, operator_inner, operator_inner, map_mul]
  · rw [← mul_assoc, inner_graph_comm, mul_assoc, ← map_mul, operator_graph_inner,
      operator_inner, operator_graph_inner, map_mul]
    rw [← mul_assoc (NaturalDualFlag.action g), action_swap, mul_assoc]
  · rw [mul_assoc, ← map_mul, operator_graph_inner, operator_graph_inner, operator_inner,
      map_mul, mul_assoc]
  · rw [mul_assoc, ← mul_assoc (MulAut.conj g), inner_graph_comm, ← mul_assoc,
      ← mul_assoc, ← pow_two, graphLinear_sq, one_mul, ← map_mul, operator_inner,
      operator_graph_inner, operator_graph_inner, map_mul]
    rw [mul_assoc, ← mul_assoc (NaturalDualFlag.action g), action_swap,
      ← mul_assoc, ← mul_assoc, swap_sq, one_mul]

/-- The constructed natural-plus-dual representation of the actual full automorphism group. -/
noncomputable def coordinateAction (hn : n = 4 ∨ n = 5) : CoordinateAction n where
  representation := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    { toFun := operator hn
      map_one' := by
        rw [← map_one (MulAut.conj : LinearGroup n →* _), operator_inner, map_one]
      map_mul' := operator_mul hn }
  on_inner g v := by
    change operator hn (MulAut.conj g) v = _
    rw [operator_inner]
    rfl
  on_graph v := by
    change operator hn (graphLinear n) v = _
    have he : graphLinear n = graphLinear n * MulAut.conj (1 : LinearGroup n) := by simp
    rw [he, operator_graph_inner, map_one, mul_one]

end BinaryNaturalDual.ModelOrbits.AutomorphismModel
