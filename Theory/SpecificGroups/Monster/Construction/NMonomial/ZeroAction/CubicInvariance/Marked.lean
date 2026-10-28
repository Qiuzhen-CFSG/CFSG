module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Assembly
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Coefficients
public import Theory.SpecificGroups.Monster.Construction.CInvariance

/-!
# Marked monomials and their standard cubic coefficients

The signed family here consists exactly of the three literal tensor families
in `ModelSpace`. Their spanning test proves a trilinear extensionality lemma.
The comparison sends their inclusion to the original Griess vectors, so the
standard coefficients and their permutation symmetry are inherited from the
fixed `griessBeta`. The specified exchange of the first and third standard
families therefore preserves all signed and reordered standard coefficients.
Literal N1 compatibility also gives cubic invariance for N1 by 28.13.

`MixedShape` and `StandardShape` describe triples; they assert neither a
support-exclusion theorem nor an orbit-reduction theorem. Those are the
remaining independent source steps.

Source: Aschbacher, *Sporadic Groups*, 9.8 and the proof of 29.9, printed
pp. 38 and 157--158. The coefficients keep the unscaled source normalization.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

/-- The literal three marked tensor families. -/
def markedVector (i : Fin 3) (x : Omega) (b : ParkerLoop) : ModelSpace :=
  ![modelOdd x b, modelTwo (pointVector x) (delta2 b),
    modelThree (pointVector x) (delta3 b)] i

/-- Signs are retained on the literal generators. -/
def signedFamily : Set ModelSpace :=
  {v | ∃ i x b, v = markedVector i x b ∨ v = -markedVector i x b}

/-- One vector in each literal source summand, with arbitrary loop labels. -/
def mixedTriple (z : Omega) (b : ParkerLoop) (x : Omega) (d : ParkerLoop)
    (y : Omega) (f : ParkerLoop) : Fin 3 → ModelSpace :=
  ![modelOdd z b, modelTwo (pointVector x) (delta2 d),
    modelThree (pointVector y) (delta3 f)]

/-- Exactly one vector from each summand, allowing signs and factor permutations. -/
def MixedShape (v : Fin 3 → ModelSpace) : Prop :=
  ∃ (z x y : Omega) (b d f : ParkerLoop) (p : Equiv.Perm (Fin 3)) (a c t : ℝ),
    (a = 1 ∨ a = -1) ∧ (c = 1 ∨ c = -1) ∧ (t = 1 ∨ t = -1) ∧
    v ∘ p = ![a • modelOdd z b, c • modelTwo (pointVector x) (delta2 d),
      t • modelThree (pointVector y) (delta3 f)]

def standardTriple (z x y : Omega) : Fin 3 → ModelSpace :=
  ![modelOdd z loopOne, modelTwo (pointVector x) (delta2 loopOne),
    modelThree (pointVector y) (delta3 loopOne)]

/-- The standard representatives, with signs and arbitrary ordering of factors. -/
def StandardShape (v : Fin 3 → ModelSpace) : Prop :=
  ∃ (z x y : Omega) (p : Equiv.Perm (Fin 3)) (a b c : ℝ),
    (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
    v ∘ p = ![a • modelOdd z loopOne,
      b • modelTwo (pointVector x) (delta2 loopOne),
      c • modelThree (pointVector y) (delta3 loopOne)]

def tripleValue (e : oddSpace ≃ₗ[ℝ] TensorTwo) (v : Fin 3 → ModelSpace) : ℝ :=
  modelBeta e (v 0) (v 1) (v 2)

theorem modelBeta_inclusion (e : oddSpace ≃ₗ[ℝ] TensorTwo) (u v w : ModelSpace) :
    modelBeta e u v w = griessBeta (modelInclusion e u) (modelInclusion e v)
      (modelInclusion e w) := rfl

theorem modelBeta_swap_left (e : oddSpace ≃ₗ[ℝ] TensorTwo) (u v w : ModelSpace) :
    modelBeta e u v w = modelBeta e v u w :=
  griessBeta_swap_left _ _ _

theorem modelBeta_swap_right (e : oddSpace ≃ₗ[ℝ] TensorTwo) (u v w : ModelSpace) :
    modelBeta e u v w = modelBeta e u w v :=
  griessBeta_swap_right _ _ _

theorem tripleValue_permute (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (p : Equiv.Perm (Fin 3)) (v : Fin 3 → ModelSpace) :
    tripleValue e (v ∘ p) = tripleValue e v :=
  griessBeta_permute p (fun i => modelInclusion e (v i))

theorem modelInclusion_odd (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (x : Omega) (b : ParkerLoop) :
    modelInclusion e (modelOdd x b) = zeroInclusion (zeroOdd x b) := by
  rw [← zeroToModel_odd e he, modelInclusion_zeroToModel]

theorem modelInclusion_two (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (a : NaturalSpace) (s : B1A2) :
    modelInclusion e (modelTwo a s) = zeroInclusion (zeroTwo a s) := by
  rw [← zeroToModel_two e, modelInclusion_zeroToModel]

theorem modelInclusion_three (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (a : NaturalSpace) (s : B1A3) :
    modelInclusion e (modelThree a s) = zeroInclusion (zeroThree a s) := by
  rw [← zeroToModel_three e, modelInclusion_zeroToModel]

theorem modelBeta_standard (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (z x y : Omega) : tripleValue e (standardTriple z x y) =
      if x = y ∧ y = z then (-5 : ℝ) / 32
      else if x = y ∨ x = z ∨ y = z then (3 : ℝ) / 32 else (-1 : ℝ) / 32 := by
  change modelBeta e (modelOdd z loopOne) (modelTwo _ _) (modelThree _ _) = _
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_two,
    modelInclusion_three, griessBeta_standard]

theorem standard_swap_odd_three (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (z x y : Omega) :
    tripleValue e (standardTriple y x z) = tripleValue e (standardTriple z x y) := by
  rw [modelBeta_standard e he, modelBeta_standard e he]
  clear he
  by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;> simp_all [eq_comm]

theorem modelBeta_swap_outer (e : oddSpace ≃ₗ[ℝ] TensorTwo) (u v w : ModelSpace) :
    modelBeta e u v w = modelBeta e w v u := by
  calc modelBeta e u v w = modelBeta e v u w := modelBeta_swap_left e u v w
       _ = modelBeta e v w u := modelBeta_swap_right e v u w
       _ = modelBeta e w v u := modelBeta_swap_left e v w u

/-- The concrete exchange preserves every signed and reordered standard coefficient. -/
theorem standardShape_invariant (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace) (g : N)
    (ho : ∀ x, ρ g (modelOdd x loopOne) =
      modelThree (pointVector x) (delta3 loopOne))
    (ht : ∀ x, ρ g (modelTwo (pointVector x) (delta2 loopOne)) =
      modelTwo (pointVector x) (delta2 loopOne))
    (hh : ∀ x, ρ g (modelThree (pointVector x) (delta3 loopOne)) = modelOdd x loopOne)
    (v : Fin 3 → ModelSpace) (hv : StandardShape v) :
    tripleValue e (fun i => ρ g (v i)) = tripleValue e v := by
  obtain ⟨z,x,y,p,a,b,c,_,_,_,hp⟩ := hv
  rw [← tripleValue_permute e p v, hp]
  rw [← tripleValue_permute e p (fun i => ρ g (v i))]
  have hp' : (fun i => ρ g (v i)) ∘ p = fun i => ρ g ((v ∘ p) i) := rfl
  rw [hp',hp]
  change modelBeta e (ρ g (a • modelOdd z loopOne))
      (ρ g (b • modelTwo (pointVector x) (delta2 loopOne)))
      (ρ g (c • modelThree (pointVector y) (delta3 loopOne))) =
    modelBeta e (a • modelOdd z loopOne)
      (b • modelTwo (pointVector x) (delta2 loopOne))
      (c • modelThree (pointVector y) (delta3 loopOne))
  simp only [map_smul,ho,ht,hh,LinearMap.smul_apply,smul_eq_mul]
  rw [modelBeta_swap_outer e (modelThree _ _) (modelTwo _ _) (modelOdd _ _)]
  exact congrArg (fun r : ℝ => c * (b * (a * r))) (standard_swap_odd_three e he z x y)

/-- Literal N1 compatibility discharges the N1 cubic-invariance branch using 28.13. -/
theorem modelBeta_n1 (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (g : N1) (u v w : ModelSpace) :
    modelBeta e (ρ g.val u) (ρ g.val v) (ρ g.val w) = modelBeta e u v w := by
  simp only [modelBeta_inclusion, hN1, CInvariance.cRepresentation_beta]

/-- The three tensor families determine any linear map from the model. -/
theorem modelSpace_ext {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f g : ModelSpace →ₗ[ℝ] M)
    (h : ∀ i x b, f (markedVector i x b) = g (markedVector i x b)) : f = g := by
  have h1 : f.comp (LinearMap.inl ℝ TensorTwo (TensorTwo × TensorThree)) =
      g.comp (LinearMap.inl ℝ TensorTwo (TensorTwo × TensorThree)) := by
    apply tensorTwo_ext
    exact h 0
  have h2 : f.comp ((LinearMap.inr ℝ TensorTwo (TensorTwo × TensorThree)).comp
      (LinearMap.inl ℝ TensorTwo TensorThree)) =
      g.comp ((LinearMap.inr ℝ TensorTwo (TensorTwo × TensorThree)).comp
        (LinearMap.inl ℝ TensorTwo TensorThree)) := by
    apply tensorTwo_ext
    exact h 1
  have h3 : f.comp ((LinearMap.inr ℝ TensorTwo (TensorTwo × TensorThree)).comp
      (LinearMap.inr ℝ TensorTwo TensorThree)) =
      g.comp ((LinearMap.inr ℝ TensorTwo (TensorTwo × TensorThree)).comp
        (LinearMap.inr ℝ TensorTwo TensorThree)) := by
    apply tensorThree_ext
    exact h 2
  apply LinearMap.ext
  intro v
  have hv : v = (v.1,0) + (0,v.2.1,0) + (0,0,v.2.2) := by simp
  rw [hv,map_add,map_add,map_add,map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (LinearMap.congr_fun h1 v.1) (LinearMap.congr_fun h2 v.2.1))
    (LinearMap.congr_fun h3 v.2.2)

/-- Trilinear equality can be tested on the actual marked signed family. -/
theorem trilinear_ext (f g : Griess.TrilinearForm ModelSpace)
    (h : ∀ u ∈ signedFamily, ∀ v ∈ signedFamily, ∀ w ∈ signedFamily,
      f u v w = g u v w) : f = g := by
  apply modelSpace_ext (M := ModelSpace →ₗ[ℝ] ModelSpace →ₗ[ℝ] ℝ)
  intro i x b
  apply modelSpace_ext (M := ModelSpace →ₗ[ℝ] ℝ)
  intro j y c
  apply modelSpace_ext (M := ℝ)
  intro k z d
  exact h _ ⟨i,x,b,Or.inl rfl⟩ _ ⟨j,y,c,Or.inl rfl⟩ _ ⟨k,z,d,Or.inl rfl⟩

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
