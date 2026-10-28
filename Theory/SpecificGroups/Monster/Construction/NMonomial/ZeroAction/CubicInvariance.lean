module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.GroupStructure
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.Marked

/-!
# Conditional monomial assembly for the zero-summand cubic

This module implements the argument of 9.8 on the actual marked signed
families. Normality of `NPlus` moves a normalizing element across an arbitrary
group element. The standard coefficient identities then prove preservation
on every nonzero monomial. Applying the same argument to the inverse rules
out creating a nonzero coefficient from a zero coefficient. Trilinearity and
the proved generation of `N` by `N1` and a marked exchange give preservation
on all of `ModelSpace`, and hence on the literal `ZeroSpace` inclusion.

The extra `NonzeroReduction` premise is deliberately explicit. It is not
part of the action/comparison contract and has not been proved here. Two
remaining source branches must discharge it: exclusion of triples without
one vector in each summand (`MixedShape`), and normalization of supported
mixed triples to `StandardShape` under the actual `NPlus` action. The final
assembly owner must supply both before asserting Aschbacher 29.9.

Source: Aschbacher, *Sporadic Groups*, Lemma 9.8, printed pp. 38--39, and
Lemma 29.9 with its full proof, printed pp. 157--158 (PDF pp. 84--85).
The cubic is always the existing pullback `modelBeta`, never a substitute.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

/-- Actual monomiality on the three signed, marked source families. -/
def IsMonomial (ρ : Representation ℝ N ModelSpace) : Prop :=
  ∀ g : N, Set.MapsTo (ρ g) signedFamily signedFamily

/-- The source orbit-reduction obligation, separate from invariance.
This predicate is not supplied by the action contract and remains to be proved. -/
def NonzeroReduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) : Prop :=
  ∀ v : Fin 3 → ModelSpace, (∀ i, v i ∈ signedFamily) → tripleValue e v ≠ 0 →
    ∃ h : NPlus, StandardShape (fun i => ρ h.val (v i))

/-- Assembly of the two independent source obligations; neither branch is
assumed to have been proved by this helper. -/
theorem nonzeroReduction_of_branches (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hSupport : ∀ v : Fin 3 → ModelSpace, (∀ i, v i ∈ signedFamily) →
      tripleValue e v ≠ 0 → MixedShape v)
    (hOrbit : ∀ v : Fin 3 → ModelSpace, MixedShape v → tripleValue e v ≠ 0 →
      ∃ h : NPlus, StandardShape (fun i => ρ h.val (v i))) : NonzeroReduction e ρ := by
  intro v hv hn
  exact hOrbit v (hSupport v hv hn) hn

private theorem action_mul (ρ : Representation ℝ N ModelSpace)
    (g h : N) (v : ModelSpace) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul]
  rfl

private theorem action_inv_cancel (ρ : Representation ℝ N ModelSpace)
    (g : N) (v : ModelSpace) : ρ g⁻¹ (ρ g v) = v := by
  rw [← action_mul, inv_mul_cancel, map_one]
  rfl

private theorem action_cancel_inv (ρ : Representation ℝ N ModelSpace)
    (g : N) (v : ModelSpace) : ρ g (ρ g⁻¹ v) = v := by
  rw [← action_mul, mul_inv_cancel, map_one]
  rfl

private theorem nonzero_invariant_of_reduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hReduce : NonzeroReduction e ρ) (g : N)
    (hstd : ∀ v, StandardShape v → tripleValue e (fun i => ρ g (v i)) = tripleValue e v)
    (v : Fin 3 → ModelSpace) (hv : ∀ i, v i ∈ signedFamily) (hn : tripleValue e v ≠ 0) :
    tripleValue e (fun i => ρ g (v i)) = tripleValue e v := by
  obtain ⟨h,hh⟩ := hReduce v hv hn
  have hc : g * h.val * g⁻¹ ∈ NPlus := nPlus_normal.conj_mem h.val h.prop g
  have heq (i : Fin 3) : ρ (g * h.val * g⁻¹) (ρ g (v i)) = ρ g (ρ h.val (v i)) := by
    rw [action_mul,action_mul,action_inv_cancel]
  calc tripleValue e (fun i => ρ g (v i)) =
      tripleValue e (fun i => ρ (g * h.val * g⁻¹) (ρ g (v i))) :=
        (modelBeta_n1 e ρ hN1 ⟨_,NPlus_le_N1 hc⟩ _ _ _).symm
    _ = tripleValue e (fun i => ρ g (ρ h.val (v i))) :=
      congrArg (tripleValue e) (funext heq)
    _ = tripleValue e (fun i => ρ h.val (v i)) := hstd _ hh
    _ = tripleValue e v := modelBeta_n1 e ρ hN1 ⟨h.val,NPlus_le_N1 h.prop⟩ _ _ _

/-- The reverse action excludes a newly nonzero coefficient, so the reduction
of nonzero monomials also controls every zero coefficient. -/
theorem signedFamily_invariant_of_reduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hmono : IsMonomial ρ) (hReduce : NonzeroReduction e ρ) (g : N)
    (hstd : ∀ v, StandardShape v → tripleValue e (fun i => ρ g (v i)) = tripleValue e v)
    (hstdInv : ∀ v, StandardShape v →
      tripleValue e (fun i => ρ g⁻¹ (v i)) = tripleValue e v)
    (v : Fin 3 → ModelSpace) (hv : ∀ i, v i ∈ signedFamily) :
    tripleValue e (fun i => ρ g (v i)) = tripleValue e v := by
  by_cases hn : tripleValue e v = 0
  · have hz : tripleValue e (fun i => ρ g (v i)) = 0 := by
      by_contra hz
      have ht := nonzero_invariant_of_reduction e ρ hN1 hReduce g⁻¹ hstdInv
        (fun i => ρ g (v i)) (fun i => hmono g (hv i)) hz
      have hi : (fun i => ρ g⁻¹ (ρ g (v i))) = v :=
        funext (fun i => action_inv_cancel ρ g (v i))
      rw [hi,hn] at ht
      exact hz ht.symm
    exact hz.trans hn.symm
  · exact nonzero_invariant_of_reduction e ρ hN1 hReduce g hstd v hv hn

private theorem inverse_exchanges (ρ : Representation ℝ N ModelSpace) (g : N)
    (ho : ∀ x, ρ g (modelOdd x loopOne) = modelThree (pointVector x) (delta3 loopOne))
    (ht : ∀ x, ρ g (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne))
    (hh : ∀ x, ρ g (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne) :
    (∀ x, ρ g⁻¹ (modelOdd x loopOne) = modelThree (pointVector x) (delta3 loopOne)) ∧
    (∀ x, ρ g⁻¹ (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne)) ∧
    (∀ x, ρ g⁻¹ (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [← hh x, action_inv_cancel]
  · intro x
    calc ρ g⁻¹ (modelTwo (pointVector x) (delta2 loopOne)) =
        ρ g⁻¹ (ρ g (modelTwo (pointVector x) (delta2 loopOne))) :=
          congrArg (ρ g⁻¹) (ht x).symm
      _ = _ := action_inv_cancel ρ g _
  · intro x
    rw [← ho x, action_inv_cancel]

/-- Concrete standard exchanges and proved orbit reduction imply preservation
for all vectors by multilinearity, including the zero coefficients. -/
theorem exchange_invariant_of_reduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hmono : IsMonomial ρ) (hReduce : NonzeroReduction e ρ) (g : N)
    (ho : ∀ x, ρ g (modelOdd x loopOne) = modelThree (pointVector x) (delta3 loopOne))
    (ht : ∀ x, ρ g (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne))
    (hh : ∀ x, ρ g (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne)
    (u v w : ModelSpace) :
    modelBeta e (ρ g u) (ρ g v) (ρ g w) = modelBeta e u v w := by
  obtain ⟨hi1,hi2,hi3⟩ := inverse_exchanges ρ g ho ht hh
  have hstd := standardShape_invariant e he ρ g ho ht hh
  have hstdInv := standardShape_invariant e he ρ g⁻¹ hi1 hi2 hi3
  have hform : Griess.pullback3 (modelBeta e) (ρ g) (ρ g) (ρ g) = modelBeta e := by
    apply trilinear_ext
    intro a ha b hb c hc
    apply signedFamily_invariant_of_reduction e ρ hN1 hmono hReduce g hstd hstdInv ![a,b,c]
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hform u) v) w

/-- The actual stabilizer of the fixed pulled-back cubic. -/
def betaStabilizer (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) : Subgroup N where
  carrier := {g | ∀ u v w, modelBeta e (ρ g u) (ρ g v) (ρ g w) = modelBeta e u v w}
  one_mem' := by
    intro u v w
    change modelBeta e (ρ 1 u) (ρ 1 v) (ρ 1 w) = modelBeta e u v w
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh u v w
    simp only [action_mul]
    exact (hg _ _ _).trans (hh u v w)
  inv_mem' := by
    intro g hg u v w
    have h := hg (ρ g⁻¹ u) (ρ g⁻¹ v) (ρ g⁻¹ w)
    simpa only [action_cancel_inv] using h.symm

/-- Conditional final assembly of the monomial argument. The additional
`NonzeroReduction` premise must be proved before claiming source 29.9. -/
theorem modelBeta_invariant_of_reduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hmono : IsMonomial ρ) (hReduce : NonzeroReduction e ρ) (w : Omega)
    (ho : ∀ x, ρ (sigma w) (modelOdd x loopOne) = modelThree (pointVector x) (delta3 loopOne))
    (ht : ∀ x, ρ (sigma w) (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne))
    (hh : ∀ x, ρ (sigma w) (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne)
    (g : N) (u v t : ModelSpace) :
    modelBeta e (ρ g u) (ρ g v) (ρ g t) = modelBeta e u v t := by
  have hn : N1 ≤ betaStabilizer e ρ := by
    intro h hh
    exact modelBeta_n1 e ρ hN1 ⟨h,hh⟩
  have hs : Subgroup.zpowers (sigma w) ≤ betaStabilizer e ρ := by
    apply Subgroup.zpowers_le.mpr
    exact exchange_invariant_of_reduction e he ρ hN1 hmono hReduce (sigma w) ho ht hh
  have hall : (⊤ : Subgroup N) ≤ betaStabilizer e ρ := by
    rw [← n1_sup_sigma w]
    exact sup_le hn hs
  exact hall (Subgroup.mem_top g) u v t

/-- The conditional argument reaches the literal zero-space inclusion.
The final source assembly must discharge `hReduce`. -/
theorem zero_beta_of_reduction (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hmono : IsMonomial ρ) (hReduce : NonzeroReduction e ρ) (w : Omega)
    (ho : ∀ x, ρ (sigma w) (modelOdd x loopOne) = modelThree (pointVector x) (delta3 loopOne))
    (ht : ∀ x, ρ (sigma w) (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne))
    (hh : ∀ x, ρ (sigma w) (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne)
    (g : N) (u v t : ZeroSpace) :
    griessBeta (zeroInclusion (representationOfModel e ρ g u))
      (zeroInclusion (representationOfModel e ρ g v))
      (zeroInclusion (representationOfModel e ρ g t)) =
      griessBeta (zeroInclusion u) (zeroInclusion v) (zeroInclusion t) :=
  representationOfModel_beta e ρ
    (modelBeta_invariant_of_reduction e he ρ hN1 hmono hReduce w ho ht hh) g u v t

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
