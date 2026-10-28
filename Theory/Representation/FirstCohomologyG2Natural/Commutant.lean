module

public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryCoordinates
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates

/-!
# Additive scalar commutants of the natural derived G₂ action

The two actual commutators from BinaryPair force an additive map to act
coordinatewise by one additive field map. The first fixes exactly the plane
spanned by e₀,e₁; the second cycles the basis in two triples. The first
commutator's equation on e₂ removes the two off-diagonal maps and identifies
the diagonal maps. A torus conjugate remains in the derived subgroup and
its (0,2) coefficient is an arbitrary nonzero field element. Commuting with
these conjugates forces the field map to be scalar multiplication.

Every characteristic-two field is included. Neither finiteness nor an
identification of G₂ with its derived subgroup is used. The final theorem
uses the original trace-zero octonion quotient and its literal derived action.
This supplies the scalar commutant input for the original-actor semilinear
geometry of Aschbacher–Smith I.2.3, printed p.413. Root and torus conventions
come from the attributed ATLAS modules imported by BinaryPair and
NaturalCoordinates; see LICENSES/ATLAS.txt.
-/

namespace Atlas.G2.Natural.Commutant

variable {F : Type*} [Field F]

private def stepA (v : Fin 6 → F) : Fin 6 → F :=
  ![v 0 + v 2 + v 5, v 1 + v 3 + v 4 + v 5,
    v 2 + v 4, v 3 + v 5, v 4, v 5]

private def stepB (v : Fin 6 → F) : Fin 6 → F :=
  ![v 3, v 5, v 1, v 4, v 0, v 2]

private def cycleB : Fin 6 → Fin 6 := ![4, 2, 5, 0, 3, 1]

private theorem fixed_stepA (v : Fin 6 → F) (hv : stepA v = v) :
    v = ![v 0, v 1, 0, 0, 0, 0] := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  change v 0 + v 2 + v 5 = v 0 at h0
  change v 1 + v 3 + v 4 + v 5 = v 1 at h1
  change v 2 + v 4 = v 2 at h2
  change v 3 + v 5 = v 3 at h3
  have hz2 : v 2 = 0 := by linear_combination h0 - h3
  have hz3 : v 3 = 0 := by linear_combination h1 - h2 - h3
  have hz4 : v 4 = 0 := by linear_combination h2
  have hz5 : v 5 = 0 := by linear_combination h3
  ext i
  fin_cases i <;> simp [hz2, hz3, hz4, hz5]

private theorem stepA_single_zero (x : F) :
    stepA (Pi.single (0 : Fin 6) x) = Pi.single 0 x := by
  ext i
  fin_cases i <;> simp [stepA]

private theorem stepA_single_one (x : F) :
    stepA (Pi.single (1 : Fin 6) x) = Pi.single 1 x := by
  ext i
  fin_cases i <;> simp [stepA]

private theorem stepA_single_two (x : F) :
    stepA (Pi.single (2 : Fin 6) x) = Pi.single 0 x + Pi.single 2 x := by
  ext i
  fin_cases i <;> simp [stepA]

private theorem stepB_single (j : Fin 6) (x : F) :
    stepB (Pi.single j x) = Pi.single (cycleB j) x := by
  fin_cases j <;> ext i <;> fin_cases i <;> simp [stepB, cycleB]

private theorem diagonal_of_commutes_pair (f : (Fin 6 → F) →+ (Fin 6 → F))
    (hA : ∀ v, f (stepA v) = stepA (f v))
    (hB : ∀ v, f (stepB v) = stepB (f v)) :
    ∃ h : F →+ F, ∀ v, f v = fun i => h (v i) := by
  classical
  let h : F →+ F := {
    toFun x := f (Pi.single (1 : Fin 6) x) 1
    map_zero' := by simp
    map_add' x y := by rw [Pi.single_add, map_add]; rfl }
  have columns (x : F) (j : Fin 6) : f (Pi.single j x) = Pi.single j (h x) := by
    let a := f (Pi.single (0 : Fin 6) x) 0
    let b := f (Pi.single (0 : Fin 6) x) 1
    let c := f (Pi.single (1 : Fin 6) x) 0
    let d := f (Pi.single (1 : Fin 6) x) 1
    have h0 : f (Pi.single (0 : Fin 6) x) = ![a,b,0,0,0,0] := by
      apply fixed_stepA
      rw [← hA, stepA_single_zero]
    have h1 : f (Pi.single (1 : Fin 6) x) = ![c,d,0,0,0,0] := by
      apply fixed_stepA
      rw [← hA, stepA_single_one]
    have hb (k : Fin 6) :
        f (Pi.single (cycleB k) x) = stepB (f (Pi.single k x)) := by
      rw [← stepB_single]
      exact hB _
    have h4 : f (Pi.single (4 : Fin 6) x) = ![0,0,b,0,a,0] := by
      have hh := hb 0
      rw [h0] at hh
      exact hh
    have h3 : f (Pi.single (3 : Fin 6) x) = ![0,0,0,a,0,b] := by
      have hh := hb 4
      rw [h4] at hh
      exact hh
    have h2 : f (Pi.single (2 : Fin 6) x) = ![0,0,d,0,c,0] := by
      have hh := hb 1
      rw [h1] at hh
      exact hh
    have h5 : f (Pi.single (5 : Fin 6) x) = ![0,0,0,c,0,d] := by
      have hh := hb 2
      rw [h2] at hh
      exact hh
    have hh := hA (Pi.single (2 : Fin 6) x)
    rw [stepA_single_two, map_add, h0, h2] at hh
    have ha : a = d := by simpa [stepA] using congrFun hh 0
    have hbc : b = c := by simpa [stepA] using congrFun hh 1
    have hc : c = 0 := by
      have h := congrFun hh 2
      change 0 + d = d + c at h
      linear_combination -h
    have hb0 : b = 0 := hbc.trans hc
    change f (Pi.single j x) = Pi.single j d
    fin_cases j
    · exact h0.trans (by ext i; fin_cases i <;> simp [ha, hb0])
    · exact h1.trans (by ext i; fin_cases i <;> simp [hc])
    · exact h2.trans (by ext i; fin_cases i <;> simp [hc])
    · exact h3.trans (by ext i; fin_cases i <;> simp [ha, hb0])
    · exact h4.trans (by ext i; fin_cases i <;> simp [ha, hb0])
    · exact h5.trans (by ext i; fin_cases i <;> simp [hc])
  refine ⟨h, fun v => ?_⟩
  have hv : f v = ∑ j : Fin 6, f (Pi.single j (v j)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [hv]
  simp_rw [columns]
  exact Finset.univ_sum_single (fun j => h (v j))

variable [CharP F 2]

private theorem equiv_eq_binaryCoordinates (v : Space F) :
    Restricted.NaturalCoordinates.equiv F v = binaryCoordinates F v := by
  obtain ⟨x, rfl⟩ := mk_surjective F v
  rfl

private theorem equiv_eq_nonbinaryCoordinates (v : Space F) (i : Fin 6) :
    Restricted.NaturalCoordinates.equiv F v i = Nonbinary.coordinates F v i := by
  obtain ⟨x, rfl⟩ := mk_surjective F v
  fin_cases i <;> rfl

private theorem coordinate_action_binaryA (v : Fin 6 → F) :
    Restricted.NaturalCoordinates.action F (binaryA F).val v = stepA v := by
  change Restricted.NaturalCoordinates.equiv F
      (derivedAction F (binaryA F) ((Restricted.NaturalCoordinates.equiv F).symm v)) = _
  simpa only [← equiv_eq_binaryCoordinates, LinearEquiv.apply_symm_apply, stepA] using
    binaryCoordinates_binaryA F ((Restricted.NaturalCoordinates.equiv F).symm v)

private theorem coordinate_action_binaryB (v : Fin 6 → F) :
    Restricted.NaturalCoordinates.action F (binaryB F).val v = stepB v := by
  change Restricted.NaturalCoordinates.equiv F
      (derivedAction F (binaryB F) ((Restricted.NaturalCoordinates.equiv F).symm v)) = _
  simpa only [← equiv_eq_binaryCoordinates, LinearEquiv.apply_symm_apply, stepB] using
    binaryCoordinates_binaryB F ((Restricted.NaturalCoordinates.equiv F).symm v)

private theorem coordinate_action_torus (l m : Fˣ) (v : Fin 6 → F) (i : Fin 6) :
    Restricted.NaturalCoordinates.action F (torus l m) v i =
      (torusWeights l m (Nonbinary.nonbinaryIndex i) : F) * v i := by
  change Restricted.NaturalCoordinates.equiv F
      (action F (torus l m) ((Restricted.NaturalCoordinates.equiv F).symm v)) i = _
  rw [equiv_eq_nonbinaryCoordinates, Nonbinary.coordinates_torus,
    ← equiv_eq_nonbinaryCoordinates, LinearEquiv.apply_symm_apply]

private theorem torus_conjugate_A_first (u : Fˣ) (v : Fin 6 → F) :
    Restricted.NaturalCoordinates.action F
      (torus 1 u * (binaryA F).val * (torus 1 u)⁻¹) v 0 =
        v 0 + (u : F) * v 2 + v 5 := by
  have hi : (torus (1 : Fˣ) u)⁻¹ = torus 1 u⁻¹ := by
    have h := (torusHom (K := F)).map_inv ((1 : Fˣ), u)
    change torus ((1 : Fˣ)⁻¹) u⁻¹ = (torus 1 u)⁻¹ at h
    simpa only [inv_one] using h.symm
  simp only [map_mul, Module.End.mul_apply]
  rw [coordinate_action_torus]
  simp only [Nonbinary.nonbinaryIndex, Matrix.cons_val_zero, torusWeights,
    Units.val_one, one_mul]
  rw [coordinate_action_binaryA]
  change (Restricted.NaturalCoordinates.action F (torus 1 u)⁻¹ v) 0 +
      (Restricted.NaturalCoordinates.action F (torus 1 u)⁻¹ v) 2 +
      (Restricted.NaturalCoordinates.action F (torus 1 u)⁻¹ v) 5 = _
  simp only [hi, coordinate_action_torus]
  simp [torusWeights, Nonbinary.nonbinaryIndex]

/-- On the actual six-coordinate natural module, every additive endomorphism
commuting with the derived G₂ action is multiplication by one field scalar.
The field need not be finite, and the derived subgroup remains literal. -/
public theorem coordinate_additive_commutant_scalar
    (f : (Fin 6 → F) →+ (Fin 6 → F))
    (hf : ∀ (g : commutator (Model F)) v,
      f (Restricted.NaturalCoordinates.action F g.val v) =
        Restricted.NaturalCoordinates.action F g.val (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  obtain ⟨h, hh⟩ := diagonal_of_commutes_pair f
    (fun v => by simpa only [coordinate_action_binaryA] using hf (binaryA F) v)
    (fun v => by simpa only [coordinate_action_binaryB] using hf (binaryB F) v)
  have hs (x : F) : h x = x * h 1 := by
    by_cases hx : x = 0
    · subst x
      simp
    let u : Fˣ := Units.mk0 x hx
    let g : commutator (Model F) :=
      ⟨torus 1 u * (binaryA F).val * (torus 1 u)⁻¹,
        (inferInstance : (commutator (Model F)).Normal).conj_mem
          (binaryA F).val (binaryA F).property (torus 1 u)⟩
    have hfirst (v : Fin 6 → F) :
        Restricted.NaturalCoordinates.action F g.val v 0 = v 0 + x * v 2 + v 5 := by
      exact torus_conjugate_A_first u v
    have he := congrFun (hf g (Pi.single (2 : Fin 6) (1 : F))) 0
    simpa [hh, hfirst, Pi.single_apply] using he
  refine ⟨h 1, fun v => ?_⟩
  rw [hh]
  ext i
  exact (hs (v i)).trans (mul_comm _ _)

end Atlas.G2.Natural.Commutant

namespace Atlas.G2.Natural

variable {F : Type*} [Field F] [CharP F 2]

/-- The additive commutant theorem on the original trace-zero octonion quotient.
The same concrete coordinate equivalence intertwines the original derived action;
no identification of full G₂ with its derived subgroup is assumed, even over F₂. -/
public theorem exists_scalar_of_additive_commutes_derived
    (f : Space F →+ Space F)
    (hf : ∀ (g : commutator (Model F)) v,
      f (derivedAction F g v) = derivedAction F g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  let e := Restricted.NaturalCoordinates.equiv F
  let f' : (Fin 6 → F) →+ (Fin 6 → F) :=
    e.toAddEquiv.toAddMonoidHom.comp (f.comp e.symm.toAddEquiv.toAddMonoidHom)
  have hf' (g : commutator (Model F)) (v : Fin 6 → F) :
      f' (Restricted.NaturalCoordinates.action F g.val v) =
        Restricted.NaturalCoordinates.action F g.val (f' v) := by
    change e (f (e.symm (e (derivedAction F g (e.symm v))))) =
      e (derivedAction F g (e.symm (e (f (e.symm v)))))
    simp only [LinearEquiv.symm_apply_apply, hf]
  obtain ⟨c, hc⟩ := Commutant.coordinate_additive_commutant_scalar f' hf'
  refine ⟨c, fun v => e.injective ?_⟩
  have h := hc (e v)
  change e (f (e.symm (e v))) = c • e v at h
  simpa only [LinearEquiv.symm_apply_apply, map_smul] using h

end Atlas.G2.Natural
