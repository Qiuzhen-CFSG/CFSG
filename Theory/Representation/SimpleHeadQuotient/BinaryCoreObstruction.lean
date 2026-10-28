module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Bruhat

/-!
# A binary linear-three obstruction to kernel containment

Let B be the actual point augmentation core U₂, S the dual natural module,
and A the image of the evaluation embedding S → B. The subrepresentation A
is simple and equivalent to S, but every equivariant map B → S vanishes.
Thus M = B, K = 0 is a counterexample to the kernel-containment conclusion
printed in Aschbacher–Smith H.6.4. The map S × B → B taking (s,b) to
pointEvaluation(s) + b gives the same obstruction for a direct-sum source.

Every point spike is in one group orbit and these spikes span the core.
Three explicit involutions in the point stabilizer have no common nonzero
fixed covector. An equivariant map to the dual therefore vanishes on every
spike, hence on the entire core. Only the existing actual Fano maps and
independently proved dual irreducibility enter this argument.

The valid replacement is quotient surjectivity, proved separately in
`Theory.Representation.SimpleHeadQuotient`; no containment in the original
kernel is asserted there. Source: H.5.3, H.6.2 and the claim H.6.4 on printed
pp.385–388 of the combined manuscript of 1 March 2004.
-/

public section

open Matrix Representation

namespace BinaryLinearThree.SimpleHeadQuotientObstruction

open FanoDecomposition

/-- Every vector of the point core is the indicated linear combination of the seven point spikes. -/
theorem pointSpike_expansion (a : Core) :
    ∑ p : Point, a.val p • pointSpike p = a := by
  apply Subtype.ext
  funext q
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    pointSpike_apply, smul_eq_mul, mul_add, mul_one, Finset.sum_add_distrib]
  have ha : ∑ p : Point, a.val p = 0 := a.property
  rw [ha, add_zero]
  simp [Pi.single_apply]

/-- Every nonzero vector is reached from the marked point by the actual SL₃(2) action. -/
theorem point_reachable (p : Point) :
    ∃ g : Group, pointPerm g Matrix.PSL3Two.flagPoint = p := by
  have hp : 0 < Fintype.card {l : Line // Matrix.PSL3Two.Fano.Incident p l} := by
    rw [Matrix.PSL3Two.Fano.lines_through_point]
    decide
  obtain ⟨⟨l, hl⟩⟩ := Fintype.card_pos_iff.mp hp
  obtain ⟨g, hg⟩ := markedFlag_reachable ⟨(p, l), hl⟩
  exact ⟨g, congrArg (fun f : Flag => f.val.1) hg⟩

/-- The actual point stabilizer has no nonzero fixed covector. -/
theorem point_stabilizer_fixed_dual_eq_zero (φ : Dual)
    (hφ : ∀ g : Group, pointPerm g Matrix.PSL3Two.flagPoint = Matrix.PSL3Two.flagPoint →
      W.dual g φ = φ) : φ = 0 := by
  let g₁ := Matrix.PSL3Two.Bruhat.upper 1
  let g₂ := Matrix.PSL3Two.Bruhat.upper 4
  let g₃ := Matrix.PSL3Two.Bruhat.perm 1
  have hi₁ : g₁⁻¹ = g₁ := inv_eq_of_mul_eq_one_right (by decide)
  have hi₂ : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right (by decide)
  have hi₃ : g₃⁻¹ = g₃ := inv_eq_of_mul_eq_one_right (by decide)
  have h₁ := congrArg (fun ψ : Dual => ψ (Pi.single 1 1)) (hφ g₁ (by decide))
  have h₂ := congrArg (fun ψ : Dual => ψ (Pi.single 2 1)) (hφ g₂ (by decide))
  have h₃ := congrArg (fun ψ : Dual => ψ (Pi.single 1 1)) (hφ g₃ (by decide))
  change φ (W g₁⁻¹ (Pi.single 1 1)) = φ (Pi.single 1 1) at h₁
  change φ (W g₂⁻¹ (Pi.single 2 1)) = φ (Pi.single 2 1) at h₂
  change φ (W g₃⁻¹ (Pi.single 1 1)) = φ (Pi.single 1 1) at h₃
  rw [hi₁, show W g₁ (Pi.single 1 1) = Pi.single 0 1 + Pi.single 1 1 by decide,
    map_add] at h₁
  rw [hi₂, show W g₂ (Pi.single 2 1) = Pi.single 1 1 + Pi.single 2 1 by decide,
    map_add] at h₂
  rw [hi₃, show W g₃ (Pi.single 1 1) = Pi.single 2 1 by decide] at h₃
  have h0 : φ (Pi.single 0 1) = 0 := add_eq_right.mp h₁
  have h1 : φ (Pi.single 1 1) = 0 := add_eq_right.mp h₂
  have h2 : φ (Pi.single 2 1) = 0 := h₃.trans h1
  apply (Pi.basisFun (ZMod 2) (Fin 3)).ext
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- Every equivariant map from the actual point core to the dual natural module is zero. -/
theorem core_to_dual_eq_zero (f : U₂.IntertwiningMap W.dual) : f = 0 := by
  have hseed : f (pointSpike Matrix.PSL3Two.flagPoint) = 0 := by
    apply point_stabilizer_fixed_dual_eq_zero
    intro g hg
    rw [← IntertwiningMap.isIntertwining U₂ W.dual f, ← pointSpike_action, hg]
  have hspike (p : Point) : f (pointSpike p) = 0 := by
    obtain ⟨g, rfl⟩ := point_reachable p
    rw [pointSpike_action, IntertwiningMap.isIntertwining U₂ W.dual f, hseed, map_zero]
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  have he := pointSpike_expansion a
  calc
    f.toLinearMap a = f (∑ p : Point, a.val p • pointSpike p) := congrArg f he.symm
    _ = 0 := by rw [map_sum]; simp only [map_smul, hspike, smul_zero, Finset.sum_const_zero]
    _ = (0 : Core →ₗ[ZMod 2] Dual) a := rfl

/-- The simple subrepresentation is identified with the actual dual module. -/
noncomputable def pointEvaluation_equiv_range :
    W.dual.Equiv pointEvaluation.range.toRepresentation :=
  Representation.Equiv.mk
    (LinearEquiv.ofInjective pointEvaluation.toLinearMap pointEvaluation_injective) (by
      intro g
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact IntertwiningMap.isIntertwining W.dual U₂ pointEvaluation g φ)

/-- The evaluation image is a simple invariant subspace of the point core. -/
theorem pointEvaluation_range_isAtom : IsAtom pointEvaluation.range := by
  let : IsIrreducible W.dual := IrreducibleCatalogue.dual_irreducible
  refine ⟨?_, ?_⟩
  · intro heq
    have hm : pointEvaluation (LinearMap.proj 0) ∈ (⊥ : Subrepresentation U₂) :=
      heq ▸ (show pointEvaluation (LinearMap.proj 0) ∈ pointEvaluation.range from ⟨_, rfl⟩)
    have hz : (LinearMap.proj 0 : Dual) = 0 :=
      pointEvaluation_injective (show pointEvaluation (LinearMap.proj 0) = pointEvaluation 0
        from hm.trans (map_zero pointEvaluation).symm)
    have he := congrArg (fun φ : Dual => φ (Pi.single 0 1)) hz
    simp at he
  · intro T hT
    let P : Subrepresentation W.dual := {
      toSubmodule := T.toSubmodule.comap pointEvaluation.toLinearMap
      apply_mem_toSubmodule g φ hφ := by
        change pointEvaluation (W.dual g φ) ∈ T
        rw [IntertwiningMap.isIntertwining W.dual U₂ pointEvaluation]
        exact T.apply_mem_toSubmodule g hφ }
    rcases eq_bot_or_eq_top P with hP | hP
    · apply le_bot_iff.mp
      intro a ha
      obtain ⟨φ, hφ⟩ := hT.le ha
      have hm : φ ∈ P := by change pointEvaluation.toLinearMap φ ∈ T; rwa [hφ]
      have hm0 : φ ∈ (⊥ : Subrepresentation W.dual) := hP ▸ hm
      have hz : φ = 0 := hm0
      show a = 0
      simpa [hz] using hφ.symm
    · apply False.elim
      apply hT.not_ge
      intro a ha
      obtain ⟨φ, rfl⟩ := ha
      have hm : φ ∈ P := by rw [hP]; trivial
      exact hm

/-- The point core has no quotient equivalent to the dual natural module. -/
theorem core_to_dual_not_surjective (f : U₂.IntertwiningMap W.dual) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (LinearMap.proj 0)
  have he := congrArg (fun φ : Dual => φ (Pi.single 0 1)) ha
  simp [core_to_dual_eq_zero f] at he

/-- The embedded dual natural module is not contained in the zero kernel. -/
theorem pointEvaluation_range_not_le_bot :
    ¬ pointEvaluation.range ≤ (⊥ : Subrepresentation U₂) := by
  intro h
  exact pointEvaluation_range_isAtom.1 (le_bot_iff.mp h)

/-- A simple embedded copy of the dual coexists with the absence of dual quotients, refuting the printed H.6.4 conclusion on the actual binary carrier. -/
theorem binary_counterexample :
    IsIrreducible pointEvaluation.range.toRepresentation ∧
    Nonempty (pointEvaluation.range.toRepresentation.Equiv W.dual) ∧
    (∀ f : U₂.IntertwiningMap W.dual, ¬ Function.Surjective f) ∧
    ¬ pointEvaluation.range ≤ (⊥ : Subrepresentation U₂) := by
  exact ⟨(Subrepresentation.irreducible_iff_isAtom _).mpr pointEvaluation_range_isAtom,
    ⟨pointEvaluation_equiv_range.symm⟩, core_to_dual_not_surjective,
    pointEvaluation_range_not_le_bot⟩

/-- The direct-sum counterexample map (s,b) ↦ pointEvaluation(s) + b. -/
noncomputable def directSumQuotient : (W.dual.prod U₂).IntertwiningMap U₂ :=
  pointEvaluation.comp (IntertwiningMap.fst (ZMod 2) W.dual U₂) +
    IntertwiningMap.snd (ZMod 2) W.dual U₂

/-- The explicit map from the direct sum onto the core is surjective. -/
theorem directSumQuotient_surjective : Function.Surjective directSumQuotient := by
  intro a
  refine ⟨(0, a), ?_⟩
  change pointEvaluation 0 + a = a
  rw [map_zero, zero_add]

/-- Even for a direct-sum source, the simple first summand need not lie in the original quotient kernel. -/
theorem directSum_first_not_in_kernel :
    ¬ (IntertwiningMap.inl (ZMod 2) W.dual U₂).range ≤ directSumQuotient.ker := by
  intro h
  apply pointEvaluation_range_not_le_bot
  intro a ha
  obtain ⟨φ, hφ⟩ := ha
  have he := h (show (φ, 0) ∈ (IntertwiningMap.inl (ZMod 2) W.dual U₂).range
    from ⟨φ, rfl⟩)
  change pointEvaluation φ + 0 = 0 at he
  show a = 0
  exact hφ.symm.trans (by simpa using he)

end BinaryLinearThree.SimpleHeadQuotientObstruction
