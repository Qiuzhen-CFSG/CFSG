module

public import Theory.Representation.SL3DoubledNaturalOffenders.Model

/-!
# The full additive commutant of doubled natural SL₃

Elementary transvections force every additive endomorphism of the natural
module commuting with SL₃ to be a field scalar. Applying this to all four
blocks computes the doubled commutant as the actual multiplicity matrix
algebra. In particular field linearity is a conclusion, not a hypothesis.

The transvection argument generalizes the existing SL₃(4) natural-block proof
in `SL3FourNaturalDual/QuadraticActors/NormalizerReduction/Centralizer.lean`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.9(3) and
B.5.10(2), printed pp.107–109.
-/

public section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix
variable {F : Type*} [Field F]

private theorem natural_transvection {i j : Fin 3} (hij : i ≠ j) (a : F)
    (v : Natural F) :
    (SpecialLinearGroup.transvection hij a).val.mulVec v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- The additive commutant on one natural copy is precisely the field scalars. -/
theorem natural_centralizer_scalar (f : Natural F →+ Natural F)
    (hf : ∀ (g : SL F) v, f (g.val.mulVec v) = g.val.mulVec (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  have hsingle {i j : Fin 3} (hij : i ≠ j) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single j 1) j) := by
    have h := hf (SpecialLinearGroup.transvection hij a) (Pi.single j 1)
    rw [natural_transvection, natural_transvection, map_add] at h
    simpa using add_left_cancel h
  have hdiag {i j : Fin 3} (hij : i ≠ j) :
      f (Pi.single i 1) i = f (Pi.single j 1) j := by
    simpa using congrFun (hsingle hij 1) i
  have hs (i : Fin 3) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single 0 1) 0) := by
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
    rw [hsingle hij]
    by_cases hj : j = 0
    · rw [hj]
    · rw [hdiag hj]
  refine ⟨f (Pi.single 0 1) 0, fun v => ?_⟩
  have hv : v = ∑ i : Fin 3, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  calc
    f v = ∑ i : Fin 3, f (Pi.single i (v i)) := by rw [← map_sum, ← hv]
    _ = ∑ i : Fin 3, Pi.single i (v i * f (Pi.single 0 1) 0) :=
      Finset.sum_congr rfl (fun i _ => hs i (v i))
    _ = f (Pi.single 0 1) 0 • v := by
      funext i
      simp [Finset.sum_apply, mul_comm]

variable [Algebra (ZMod 2) F]

private theorem representation_single (g : SL F) (j : Fin 2) (v : Natural F) :
    representation F g (Pi.single j v) = Pi.single j (g.val.mulVec v) := by
  funext i
  by_cases hi : i = j <;> simp [hi, Pi.single_eq_of_ne]

/-- Every binary map commuting with the doubled component is a multiplicity
matrix. This includes all off-diagonal maps between the natural copies. -/
theorem centralizer_multiplicity (f : Module.End (ZMod 2) (Space F))
    (hf : ∀ (g : SL F) v, f (representation F g v) = representation F g (f v)) :
    ∃ c : Matrix (Fin 2) (Fin 2) F, f = multiplicity F c := by
  let block (i j : Fin 2) : Natural F →+ Natural F :=
    { toFun := fun v => f (Pi.single j v) i
      map_zero' := by simp
      map_add' v w := by simp [Pi.single_add] }
  have hb (i j : Fin 2) (g : SL F) (v : Natural F) :
      block i j (g.val.mulVec v) = g.val.mulVec (block i j v) := by
    change f (Pi.single j (g.val.mulVec v)) i = g.val.mulVec (f (Pi.single j v) i)
    rw [← representation_single]
    exact congrFun (hf g (Pi.single j v)) i
  choose c hc using fun i j => natural_centralizer_scalar (block i j) (hb i j)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    funext i
    fin_cases i <;> simp
  funext i
  have he : f v i = f (Pi.single 0 (v 0)) i + f (Pi.single 1 (v 1)) i := by
    conv_lhs => rw [hv, map_add]
    rfl
  exact he.trans (congrArg₂ (· + ·) (hc i 0 (v 0)) (hc i 1 (v 1)))

/-- Exact coverage and uniqueness for the full binary commutant. -/
theorem commutes_iff_multiplicity (f : Module.End (ZMod 2) (Space F)) :
    (∀ (g : SL F) v, f (representation F g v) = representation F g (f v)) ↔
      ∃! c : Matrix (Fin 2) (Fin 2) F, f = multiplicity F c := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := centralizer_multiplicity f hf
    exact ⟨c, hc, fun d hd => multiplicity_injective F (hd.symm.trans hc)⟩
  · rintro ⟨c, rfl, _⟩ g v
    exact LinearMap.congr_fun (multiplicity_commutes F c g) v

/-- An actual centralizing ambient unit has an invertible multiplicity matrix. -/
theorem centralizer_units (b : Ambient F)
    (hb : b ∈ Subgroup.centralizer (component F : Set (Ambient F))) :
    ∃ c : (Matrix (Fin 2) (Fin 2) F)ˣ, (b : Module.End (ZMod 2) (Space F)) =
      multiplicity F c.val := by
  have hex (a : Ambient F) (ha : a ∈ Subgroup.centralizer (component F : Set (Ambient F))) :
      ∃ c : Matrix (Fin 2) (Fin 2) F, (a : Module.End (ZMod 2) (Space F)) =
        multiplicity F c := by
    apply centralizer_multiplicity
    intro g v
    have he := (Subgroup.mem_centralizer_iff.mp ha) ((representation F).asGroupHom g) ⟨g, rfl⟩
    exact LinearMap.congr_fun (congrArg Units.val he.symm) v
  obtain ⟨c, hc⟩ := hex b hb
  obtain ⟨d, hd⟩ := hex b⁻¹ ((Subgroup.centralizer _).inv_mem hb)
  have hcd : c * d = 1 := by
    apply multiplicity_injective F
    rw [multiplicity_mul, ← hc, ← hd, multiplicity_one]
    exact b.val_inv
  have hdc : d * c = 1 := by
    apply multiplicity_injective F
    rw [multiplicity_mul, ← hd, ← hc, multiplicity_one]
    exact b.inv_val
  exact ⟨⟨c, d, hcd, hdc⟩, hc⟩

/-- The center of the full binary commutant recovers the original field scalars. -/
theorem commutant_center_scalar (f : Module.End (ZMod 2) (Space F))
    (hf : ∀ (g : SL F) v, f (representation F g v) = representation F g (f v))
    (hc : ∀ c : Matrix (Fin 2) (Fin 2) F,
      multiplicity F c * f = f * multiplicity F c) :
    ∃ a : F, ∀ v, f v = a • v := by
  obtain ⟨c, rfl⟩ := centralizer_multiplicity f hf
  have hs : c ∈ Set.range (Matrix.scalar (Fin 2)) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j _
    apply multiplicity_injective F
    simpa only [multiplicity_mul] using hc (Matrix.single i j 1)
  obtain ⟨a, rfl⟩ := hs
  refine ⟨a, fun v => ?_⟩
  funext i j
  fin_cases i <;> simp [multiplicity, Matrix.scalar_apply, Matrix.diagonal_apply]

end Representation.SL3DoubledNaturalOffenders
