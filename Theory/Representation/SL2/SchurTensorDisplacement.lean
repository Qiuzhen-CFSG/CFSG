module

public import Theory.Representation.SL2.SchurTensorDisplacement.Exchange
public import Theory.Representation.SchurDisplacement.MarkedAction

/-!
# Descent of paired-tensor displacement

An actual equivalence from a scalar-extended representation to a Frobenius
pair carries the given outer intertwiner to an involutory exchange. The
exchange calculation bounds displacement there. Kernel base change and
rank-nullity descend it to the original coefficient field; the tower law
then descends both the space and its literal displacement image together.

The Chapter K consumer uses the original marked Schur field and its actual
Schur-linear operator. The tensor equivalence remains an explicit input here;
this module does not assert that every highest-weight module has such a form.
Source: Guralnick--Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2), manuscript pp.20,22; Aschbacher--Smith K.3.1, pp.453--454.
-/

public section

open scoped TensorProduct MonoidAlgebra
open Module
namespace Representation.SL2.SchurTensorDisplacement
noncomputable section

section Scalars
variable {k E F W : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra E F]
  [AddCommGroup W] [Module E W] [Module k W] [IsScalarTower k E W]
  [FiniteDimensional E W]

omit [Field k] [Algebra k E] [Module k W] [IsScalarTower k E W] in
/-- Extension of the coefficient field preserves displacement rank. -/
theorem displacement_rank_baseChange (T : Module.End E W) :
    finrank F (T.baseChange F - 1).range = finrank E (T - 1).range := by
  have hk := LinearMap.FixedSpaceTransport.finrank_ker_baseChange (E := F) (T - 1)
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_one] at hk
  have hW := (T - 1).finrank_range_add_finrank_ker
  have hF := (T.baseChange F - 1).finrank_range_add_finrank_ker
  rw [Module.finrank_baseChange] at hF
  omega

/-- A displacement bound over an extension descends through the original
coefficient field, retaining its actual restriction of scalars. -/
theorem displacement_bound_descends (T : Module.End E W) (b : ℕ)
    (h : finrank F (F ⊗[E] W) ≤ b * finrank F (T.baseChange F - 1).range) :
    finrank k W ≤ b * finrank k (T.restrictScalars k - 1).range := by
  rw [Module.finrank_baseChange, displacement_rank_baseChange] at h
  let e : (T - 1).range ≃ₗ[k] (T.restrictScalars k - 1).range :=
    { toFun := fun v => ⟨v.val, v.property⟩
      invFun := fun v => ⟨v.val, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hh := Nat.mul_le_mul_left (finrank k E) h
  rw [← mul_assoc, mul_comm (finrank k E) b, mul_assoc,
    Module.finrank_mul_finrank, Module.finrank_mul_finrank, e.finrank_eq] at hh
  exact hh
end Scalars


private theorem irreducible_of_equiv {F H U W : Type*} [Field F] [Monoid H]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    {ρ : Representation F H U} {σ : Representation F H W}
    (e : ρ.Equiv σ) (hσ : IsIrreducible σ) : IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

section PairDescent
variable {k E F H W : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra E F]
  [CharP F 2] [IsAlgClosed F] [Group H]
  [AddCommGroup W] [Module E W] [Module k W] [IsScalarTower k E W]
  [FiniteDimensional E W]

/-- A genuine paired tensor equivalence after scalar extension bounds the
original operator, over its original smaller field. -/
theorem involution_bound_of_paired_scalarExtension
    (ρ : Representation E H W) [IsIrreducible (extendScalars F ρ)]
    (δ : MulAut H) (hδ : δ ^ 2 = 1) (c : H) (T : Module.End E W)
    (h2 : T * T = 1) (hT : ∀ a, T * ρ a = ρ (c * δ a * c⁻¹) * T)
    {d : ℕ} (hd : 2 ≤ d) (τ : Representation F H (Fin d → F))
    (φ : (extendScalars F ρ).Equiv (τ.tprod (τ.comp δ.toMonoidHom))) :
    finrank k W ≤ 4 * finrank k (T.restrictScalars k - 1).range := by
  let π := τ.tprod (τ.comp δ.toMonoidHom)
  let : IsIrreducible π := irreducible_of_equiv φ.symm inferInstance
  let e := φ.toLinearEquiv
  let T' := e.conjRingEquiv (T.baseChange F)
  have heρ (a : H) : e.conjRingEquiv (extendScalars F ρ a) = π a := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e ((extendScalars F ρ a) (e.symm (e w))) = π a (e w)
    rw [e.symm_apply_apply]
    exact IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap a w
  have hbase (a : H) : T.baseChange F * extendScalars F ρ a =
      extendScalars F ρ (c * δ a * c⁻¹) * T.baseChange F := by
    change T.baseChange F * (ρ a).baseChange F =
      (ρ (c * δ a * c⁻¹)).baseChange F * T.baseChange F
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hT]
  have hT' (a : H) : T' * π a = π (c * δ a * c⁻¹) * T' := by
    have hh := congrArg e.conjRingEquiv (hbase a)
    simpa only [map_mul, heρ] using hh
  have h2' : T' * T' = 1 := by
    change e.conjRingEquiv _ * e.conjRingEquiv _ = 1
    rw [← map_mul, ← LinearMap.baseChange_mul, h2, LinearMap.baseChange_one, map_one]
  have hb := paired_involution_bound hd τ δ hδ c T' h2' hT'
  have hr := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv e
    (T.baseChange F) T' (by
      intro v
      change e (T.baseChange F v) = e (T.baseChange F (e.symm (e v)))
      rw [e.symm_apply_apply])
  rw [← e.finrank_eq, ← hr] at hb
  exact displacement_bound_descends (k := k) T 4 hb
end PairDescent
end
end Representation.SL2.SchurTensorDisplacement
