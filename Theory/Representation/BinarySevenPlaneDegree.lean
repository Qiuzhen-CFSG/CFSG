module

public import Theory.Representation.BinarySevenPlaneDegree.Descent
public import Theory.Representation.BinarySevenPlaneDegree.PlaneActions
public import Theory.Representation.AbelianWeightAutomizer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Binary degree at least twenty-four from a quaternion seven-plane

Restrict a faithful binary representation to the marked elementary abelian
subgroup of order 49 and extend scalars to an algebraic closure. Faithfulness
supplies a nontrivial occurring character. Inverse ambient conjugations and
binary Frobenius give the twenty-four pullbacks constructed in `PlaneActions`.
Their characters are distinct, so the independent character spaces give the
dimension bound. No irreducibility or finiteness of the ambient group is needed.

This proves the representation ingredient for the q = 2 triality exclusion
in Aschbacher--Smith, G.9.3, printed p.356. The actual marked subgroup in the
triality carrier is a separate construction, not a hypothesis about weights
or representation degree.
-/

public section

namespace Representation.BinarySevenPlaneDegree
variable {E G H V : Type*} [Field E] [Group G] [Group H]
  [AddCommGroup V] [Module E V]

private lemma embedding_pullback_occurs (rho : Representation E G V) (e : H →* G)
    (g : G) (a : H →* H) (ha : ∀ z, g * e z * g⁻¹ = e (a z))
    (chi : H →* Eˣ) (hchi : characterWeightSpace (rho.comp e) chi ≠ ⊥) :
    characterWeightSpace (rho.comp e) (chi.comp a) ≠ ⊥ := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hchi
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨rho g⁻¹ v, ?_, ?_⟩
  · simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv ⊢
    intro z
    have hc : e z * g⁻¹ = g⁻¹ * e (a z) := by rw [← ha]; group
    change rho (e z) (rho g⁻¹ v) = (chi (a z) : E) • rho g⁻¹ v
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    rw [show rho (e (a z)) v = (chi (a z) : E) • v from hv (a z)]
    exact map_smul _ _ _
  · intro hz
    have he := congrArg (rho g) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he
    exact hn he

open QuaternionSevenPlane

private lemma pullback_pow_occurs (sigma : Representation E (Multiplicative Plane) V)
    (f : Module.End (ZMod 7) Plane)
    (hf : ∀ chi, characterWeightSpace sigma chi ≠ ⊥ →
      characterWeightSpace sigma (pullback chi f) ≠ ⊥)
    (chi : Multiplicative Plane →* Eˣ) (hchi : characterWeightSpace sigma chi ≠ ⊥)
    (n : ℕ) : characterWeightSpace sigma (pullback chi (f ^ n)) ≠ ⊥ := by
  induction n with
  | zero => simpa only [pow_zero, pullback_one] using hchi
  | succ n hn =>
    rw [pow_succ, ← pullback_mul]
    exact hf _ hn

end Representation.BinarySevenPlaneDegree

namespace Representation.BinarySevenPlaneDegree
open QuaternionSevenPlane
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private lemma orbit_occurs {E : Type*} [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    (rho : Representation (ZMod 2) G V) (d : Data G)
    (chi : Multiplicative Plane →* Eˣ)
    (hchi : characterWeightSpace ((rho.extendScalars E).comp d.embedding) chi ≠ ⊥)
    (i : OrbitIndex) :
    characterWeightSpace ((rho.extendScalars E).comp d.embedding)
      (pullback chi (orbitMap i)) ≠ ⊥ := by
  let sigma := (rho.extendScalars E).comp d.embedding
  have hf : ∀ c, characterWeightSpace sigma c ≠ ⊥ →
      characterWeightSpace sigma (pullback c firstLinear) ≠ ⊥ := by
    intro c hc
    exact embedding_pullback_occurs (rho.extendScalars E) d.embedding d.first
      (AddMonoidHom.toMultiplicative firstLinear.toAddMonoidHom)
      (fun z => d.first_conjugation (Multiplicative.toAdd z)) c hc
  have hs : ∀ c, characterWeightSpace sigma c ≠ ⊥ →
      characterWeightSpace sigma (pullback c secondLinear) ≠ ⊥ := by
    intro c hc
    exact embedding_pullback_occurs (rho.extendScalars E) d.embedding d.second
      (AddMonoidHom.toMultiplicative secondLinear.toAddMonoidHom)
      (fun z => d.second_conjugation (Multiplicative.toAdd z)) c hc
  have hd : ∀ c, characterWeightSpace sigma c ≠ ⊥ →
      characterWeightSpace sigma (pullback c doubleLinear) ≠ ⊥ := by
    intro c hc
    rw [pullback_double]
    exact frobenius_occurs (rho.comp d.embedding) c hc
  rw [orbitMap, ← pullback_mul, ← pullback_mul]
  exact pullback_pow_occurs sigma _ hd _
    (pullback_pow_occurs sigma _ hs _ (pullback_pow_occurs sigma _ hf chi hchi _) _) _

/-- A faithful binary representation of a group containing the marked seven-plane
has dimension at least twenty-four. -/
theorem finrank_ge [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (hrho : Function.Injective rho) (d : Data G) :
    24 ≤ Module.finrank (ZMod 2) V := by
  classical
  let E := AlgebraicClosure (ZMod 2)
  let sigma := (rho.extendScalars E).comp d.embedding
  have hsigma : Function.Injective sigma :=
    ((extendScalars_faithful_iff E rho).mp hrho).comp d.embedding_injective
  have hcard : Nat.card (Multiplicative Plane) = 49 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Plane))]
    simp [Plane]
  have horder : (Nat.card (Multiplicative Plane) : E) ≠ 0 := by
    rw [hcard]
    intro hz
    exact (by decide : ¬ 2 ∣ 49) ((CharP.cast_eq_zero_iff E 2 49).mp hz)
  have hchi : ∃ chi : CharacterWeight sigma, chi.val ≠ 1 := by
    by_contra! h
    have hsep : (Multiplicative.ofAdd (1, 0) : Multiplicative Plane) = 1 := by
      apply eq_of_characterWeight_values sigma hsigma horder
      intro chi
      simp [h chi]
    have : (1 : ZMod 7) = 0 := congrArg (fun z => (Multiplicative.toAdd z).1) hsep
    exact (one_ne_zero : (1 : ZMod 7) ≠ 0) this
  obtain ⟨chi, hchi⟩ := hchi
  let orbit : OrbitIndex → CharacterWeight sigma := fun i =>
    ⟨pullback chi.val (orbitMap i), orbit_occurs rho d chi.val chi.property i⟩
  have hinj : Function.Injective orbit := by
    intro i j hij
    exact orbit_pullback_injective chi.val hchi (congrArg Subtype.val hij)
  obtain ⟨hfinite, hbound⟩ := characterWeight_card_le sigma horder
  let := hfinite
  have hc := (Nat.card_le_card_of_injective _ hinj).trans hbound
  simpa only [OrbitIndex, Nat.card_prod, Nat.card_fin, Module.finrank_baseChange] using hc
end Representation.BinarySevenPlaneDegree
