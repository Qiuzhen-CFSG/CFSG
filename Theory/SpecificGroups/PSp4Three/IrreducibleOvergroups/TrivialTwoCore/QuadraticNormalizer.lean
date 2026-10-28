module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Reduction
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
import Mathlib.Tactic.FinCases

/-!
# An explicit quadratic extension normalizer in Sp₄(3)

On the ordered coordinates `(x₀,x₁,y₀,y₁)`, the operator
`J(x₀,x₁,y₀,y₁) = (-x₁,x₀,y₁,-y₀)` squares to minus the identity and is
self-adjoint for the alternating form. It has no eigenvector over the
three-element field, so each nonzero vector and its image are independent.

The symplectic maps conjugating `J` to `J` or `-J` form an actual subgroup.
Central scalar maps lie in it; consequently taking its projective image and
then the full symplectic preimage returns precisely this subgroup. A coordinate
transvection proves that its projective image is proper.

These constructions give a concrete interface for a quadratic extension route
to the six-point action. Neither coverage of maximal subgroups by conjugates
of this normalizer nor its six-point action is asserted here. The restriction
lemma at the end constructs an action only from an explicitly supplied faithful
action of this particular projective subgroup.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. For the exceptional comparison
needed by the remaining action construction, see the actual PSL₂(9)–A₆
comparison in `Theory.AtlasPort.ExceptionalIsomorphisms.Order360`.
-/

@[expose] public section

noncomputable section

namespace Matrix.PSp4Three.TrivialTwoCore

/-- The actual four-dimensional ternary symplectic module. -/
abbrev V := Vector 2 (ZMod 3)

/-- Multiplication by a square root of minus one on both hyperbolic halves. -/
def quadraticOperator : Module.End (ZMod 3) V where
  toFun x := Sum.elim ![-x (.inl 1), x (.inl 0)] ![x (.inr 1), -x (.inr 0)]
  map_add' x y := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [add_comm]
  map_smul' a x := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp

theorem quadraticOperator_square (x : V) : quadraticOperator (quadraticOperator x) = -x := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [quadraticOperator]

theorem quadraticOperator_selfadjoint (x y : V) :
    form (quadraticOperator x) y = form x (quadraticOperator y) := by
  simp [form_apply, Fin.sum_univ_two, quadraticOperator]
  ring

theorem quadraticOperator_not_scalar (a : ZMod 3) :
    quadraticOperator (e 0) ≠ a • e 0 := by
  intro h
  have h' := congrFun h (.inl 1)
  simp [quadraticOperator, e] at h'

theorem quadraticOperator_no_eigenvector {x : V} (hx : x ≠ 0) (a : ZMod 3) :
    quadraticOperator x ≠ a • x := by
  intro h
  have hs := congrArg quadraticOperator h
  rw [quadraticOperator_square, map_smul, h, smul_smul] at hs
  have ha : (-1 : ZMod 3) = a * a :=
    smul_left_injective (ZMod 3) hx (by simpa only [neg_one_smul] using hs)
  exact (by decide : ∀ a : ZMod 3, a * a ≠ -1) a ha.symm

theorem quadraticOperator_pair_independent {x : V} (hx : x ≠ 0) :
    LinearIndependent (ZMod 3) ![x, quadraticOperator x] := by
  rw [LinearIndependent.pair_iff' hx]
  intro a h
  exact quadraticOperator_no_eigenvector hx a h.symm

private theorem smul_scalar (g : Sp 2 (ZMod 3)) (a : ZMod 3) (x : V) :
    g • (a • x) = a • (g • x) := (toLinear g).map_smul a x

/-- Symplectic maps conjugating the explicit quadratic operator to itself or its negative. -/
def quadraticNormalizer : Subgroup (Sp 2 (ZMod 3)) where
  carrier := {g | ∃ a : ZMod 3, a * a = 1 ∧
    ∀ x : V, g • quadraticOperator x = a • quadraticOperator (g • x)}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hg⟩ ⟨b, hb, hh⟩
    refine ⟨a * b, ?_, ?_⟩
    · calc
        (a * b) * (a * b) = (a * a) * (b * b) := by ring
        _ = 1 := by rw [ha, hb, one_mul]
    · intro x
      simp only [mul_smul g h, hh, smul_scalar, hg, smul_smul b a, mul_comm b a]
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    intro x
    have h := congrArg (fun y : V => g⁻¹ • y) (hg (g⁻¹ • x))
    simp only [smul_inv_smul, inv_smul_smul, smul_scalar] at h
    rw [h, smul_smul, ha, one_smul]

theorem mem_quadraticNormalizer_iff (g : Sp 2 (ZMod 3)) :
    g ∈ quadraticNormalizer ↔
      (∀ x : V, g • quadraticOperator x = quadraticOperator (g • x)) ∨
      (∀ x : V, g • quadraticOperator x = -quadraticOperator (g • x)) := by
  constructor
  · rintro ⟨a, ha, h⟩
    rcases mul_self_eq_one_iff.mp ha with rfl | rfl
    · exact Or.inl (by simpa only [one_smul] using h)
    · exact Or.inr (by simpa only [neg_one_smul] using h)
  · rintro (h | h)
    · exact ⟨1, one_mul _, by simpa only [one_smul] using h⟩
    · exact ⟨-1, by simp, by simpa only [neg_one_smul] using h⟩

theorem center_le_quadraticNormalizer :
    Subgroup.center (Sp 2 (ZMod 3)) ≤ quadraticNormalizer := by
  intro g hg
  obtain ⟨a, ha⟩ := central_is_scalar g hg
  refine ⟨1, one_mul _, ?_⟩
  intro x
  rw [ha, ha, one_smul, map_smul]

/-- The image of the actual quadratic normalizer under the central quotient. -/
def projectiveQuadraticNormalizer : Subgroup (PSp 2 (ZMod 3)) :=
  quadraticNormalizer.map projection

/-- The full preimage is exactly the normalizer, since it contains every central scalar. -/
theorem fullPreimage_projectiveQuadraticNormalizer :
    fullPreimage projectiveQuadraticNormalizer = quadraticNormalizer := by
  apply Subgroup.comap_map_eq_self
  rw [projection_kernel]
  exact center_le_quadraticNormalizer

theorem le_projectiveQuadraticNormalizer_iff (M : Subgroup (PSp 2 (ZMod 3))) :
    M ≤ projectiveQuadraticNormalizer ↔ fullPreimage M ≤ quadraticNormalizer := by
  constructor
  · intro h
    rw [← fullPreimage_projectiveQuadraticNormalizer]
    exact Subgroup.comap_mono h
  · intro h x hx
    obtain ⟨g, rfl⟩ := projection_surjective x
    exact ⟨g, h hx, rfl⟩

/-- The transvection in the first coordinate direction does not normalize this field structure. -/
theorem projectiveQuadraticNormalizer_ne_top : projectiveQuadraticNormalizer ≠ ⊤ := by
  intro htop
  have ht : transvection (e (F := ZMod 3) (n := 2) 0) 1 ∈ quadraticNormalizer := by
    rw [← fullPreimage_projectiveQuadraticNormalizer]
    change projection _ ∈ projectiveQuadraticNormalizer
    rw [htop]
    trivial
  obtain ⟨a, ha, ht⟩ := ht
  have h := congrFun (ht (f 0)) (.inl 1)
  have ha0 : a = 0 := by
    simpa [quadraticOperator, transvection_apply, form_apply, Fin.sum_univ_two,
      e, f, Pi.single_apply] using h.symm
  simp [ha0] at ha

/-- Restrict a genuine faithful action along containment in a conjugate. -/
theorem exists_faithful_sixPointAction_of_conjugate
    (hmodel : ∃ f : projectiveQuadraticNormalizer →* Equiv.Perm (Fin 6),
      Function.Injective f)
    (M : Subgroup (PSp 2 (ZMod 3)))
    (hM : ∃ g : PSp 2 (ZMod 3),
      M ≤ projectiveQuadraticNormalizer.map (MulAut.conj g).toMonoidHom) :
    ∃ f : M →* Equiv.Perm (Fin 6), Function.Injective f := by
  obtain ⟨f, hf⟩ := hmodel
  obtain ⟨g, hg⟩ := hM
  let c := (MulAut.conj g).subgroupMap projectiveQuadraticNormalizer
  exact ⟨(f.comp c.symm.toMonoidHom).comp (Subgroup.inclusion hg),
    hf.comp (c.symm.injective.comp (Subgroup.inclusion_injective hg))⟩

end Matrix.PSp4Three.TrivialTwoCore
