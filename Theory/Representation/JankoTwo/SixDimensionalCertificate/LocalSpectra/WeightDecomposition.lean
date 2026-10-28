module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.WeightSpaces
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Simultaneous weights for the literal Hall--Janko order-five pair

The separable annihilator X⁵−1 gives simultaneous eigenspace decomposition.
The inverse normalizer rotates these spaces, and faithfulness excludes support
only at the zero weight. The finite certificate therefore gives one orbit of
six one-dimensional spaces. No irreducibility or module catalogue is assumed.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected
Table 2, the characteristic-two degree-six J₂ entry. See ../Source.md.
-/

@[expose] public noncomputable section

namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
open Sporadic.LeechRelated.J2 Polynomial
open scoped BigOperators DirectSum
variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

def weightSpace (ρ : Representation E Carrier U) (ζ : E) (w : Weights.Weight) :
    Submodule E U :=
  Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ w.1.val) ⊓
    Module.End.eigenspace (ρ TraceGeometry.y) (ζ ^ w.2.val)

@[simp] theorem finrank_weightSpace (ρ : Representation E Carrier U) (ζ : E)
    (w : Weights.Weight) : Module.finrank E (weightSpace ρ ζ w) = weightMultiplicity ρ ζ w := rfl

private theorem fifth_semisimple [CharP E 2] (f : Module.End E U) (hf : f ^ 5 = 1) :
    f.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : E[X]) ^ 5 - 1)
  · apply (Polynomial.X_pow_sub_one_separable_iff.mpr ?_).squarefree
    exact (CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide)
  · simp [hf]

/-- A nonzero eigenspace of an operator of exponent five has a fifth-root eigenvalue. -/
theorem eigenvalue_fifth_power (f : Module.End E U) (hf : f ^ 5 = 1)
    {a : E} (ha : f.eigenspace a ≠ ⊥) : a ^ 5 = 1 := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have hev : f.HasEigenvector a v := ⟨hv, hn⟩
  apply smul_left_injective E hn
  simpa [hf] using (hev.pow_apply 5).symm

private def pairOperator (ρ : Representation E Carrier U) : Bool → Module.End E U :=
  fun b => if b then ρ TraceGeometry.y else ρ TraceGeometry.x

private theorem pair_pow (ρ : Representation E Carrier U) (b : Bool) :
    pairOperator ρ b ^ 5 = 1 := by
  cases b <;> simp [pairOperator, ← map_pow, TraceGeometry.x_pow_five, TraceGeometry.y_pow_five]

private theorem pair_commute (ρ : Representation E Carrier U) (a b : Bool) :
    Commute (pairOperator ρ a) (pairOperator ρ b) := by
  have h : Commute (ρ TraceGeometry.x) (ρ TraceGeometry.y) := by
    change ρ TraceGeometry.x * ρ TraceGeometry.y = ρ TraceGeometry.y * ρ TraceGeometry.x
    rw [← map_mul, ← map_mul, TraceGeometry.x_y_commute]
  cases a <;> cases b
  · exact Commute.refl _
  · exact h
  · exact h.symm
  · exact Commute.refl _

private theorem pair_max_eq [CharP E 2] (ρ : Representation E Carrier U) (b : Bool) (a : E) :
    (pairOperator ρ b).maxGenEigenspace a = (pairOperator ρ b).eigenspace a :=
  (fifth_semisimple _ (pair_pow ρ b)).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a

private def weightValues (ζ : E) (w : Weights.Weight) : Bool → E :=
  fun b => if b then ζ ^ w.2.val else ζ ^ w.1.val

private theorem weightSpace_eq (ρ : Representation E Carrier U) (ζ : E) (w : Weights.Weight) :
    weightSpace ρ ζ w = ⨅ b, (pairOperator ρ b).eigenspace (weightValues ζ w b) := by
  simp [weightSpace, pairOperator, weightValues, iInf_bool_eq, inf_comm]

/-- The actual twenty-five simultaneous spaces are independent. -/
theorem weightSpace_independent [CharP E 2] (ρ : Representation E Carrier U)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) : iSupIndep (weightSpace ρ ζ) := by
  have hi : iSupIndep (fun χ : Bool → E => ⨅ b, (pairOperator ρ b).eigenspace (χ b)) := by
    simpa only [pair_max_eq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (pairOperator ρ)
        (fun a b t => Module.End.mapsTo_maxGenEigenspace_of_comm (pair_commute ρ b a) t)
  have hj : Function.Injective (weightValues ζ) := by
    intro a b h
    apply Prod.ext
    · apply ZMod.val_injective 5
      exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (congrFun h false)
    · apply ZMod.val_injective 5
      exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (congrFun h true)
  simpa only [Function.comp_def, ← weightSpace_eq] using hi.comp hj

/-- The actual twenty-five simultaneous spaces span the representation. -/
theorem iSup_weightSpace_eq_top [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    (⨆ w, weightSpace ρ ζ w) = ⊤ := by
  have ht : (⨆ χ : Bool → E, ⨅ b, (pairOperator ρ b).eigenspace (χ b)) = ⊤ := by
    have hsingle : ∀ b, ⨆ a, (pairOperator ρ b).maxGenEigenspace a = ⊤ := by
      intro b
      simpa only [pair_max_eq] using
        (fifth_semisimple _ (pair_pow ρ b)).iSup_eigenspace_eq_top
    simpa only [pair_max_eq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        (pairOperator ρ) (fun a b _ => pair_commute ρ a b) hsingle
  apply top_unique
  rw [← ht]
  refine iSup_le fun χ => ?_
  by_cases hχ : (⨅ b, (pairOperator ρ b).eigenspace (χ b)) = ⊥
  · simp [hχ]
  have hn (b : Bool) : (pairOperator ρ b).eigenspace (χ b) ≠ ⊥ := by
    intro hb
    exact hχ (bot_unique (le_trans (iInf_le _ b) (le_of_eq hb)))
  obtain ⟨a, ha, hpa⟩ := hζ.eq_pow_of_pow_eq_one
    (eigenvalue_fifth_power _ (pair_pow ρ false) (hn false))
  obtain ⟨b, hb, hpb⟩ := hζ.eq_pow_of_pow_eq_one
    (eigenvalue_fifth_power _ (pair_pow ρ true) (hn true))
  have heq : (⨅ t, (pairOperator ρ t).eigenspace (χ t)) =
      weightSpace ρ ζ ((a : ZMod 5), (b : ZMod 5)) := by
    simp [weightSpace, pairOperator, iInf_bool_eq,
      ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb, hpa, hpb, inf_comm]
  rw [heq]
  exact le_iSup _ _

/-- Simultaneous decomposition for the literal order-five pair. -/
theorem weightSpace_isInternal [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    DirectSum.IsInternal (weightSpace ρ ζ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (weightSpace_independent ρ hζ) (iSup_weightSpace_eq_top ρ hζ)

/-- The multiplicities sum to the degree, with no decomposition premise. -/
theorem sum_weightMultiplicity [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    ∑ w, weightMultiplicity ρ ζ w = Module.finrank E U := by
  classical
  have he := (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace ρ ζ))
    (weightSpace_isInternal ρ hζ)).finrank_eq
  simpa only [Module.finrank_directSum, finrank_weightSpace] using he

/-- Faithfulness prevents the simultaneous fixed space from being the whole module. -/
theorem weightMultiplicity_zero_lt [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ) (ζ : E) :
    weightMultiplicity ρ ζ 0 < Module.finrank E U := by
  apply Submodule.finrank_lt
  intro htop
  change weightSpace ρ ζ 0 = ⊤ at htop
  apply TraceGeometry.x_ne_one
  apply hρ
  rw [map_one]
  ext v
  have hv : v ∈ weightSpace ρ ζ 0 := by rw [htop]; trivial
  simpa [weightSpace, Module.End.mem_eigenspace_iff] using hv.1

private theorem action_injective (ρ : Representation E Carrier U) (g : Carrier) :
    Function.Injective (ρ g) := by
  intro a b h
  have hh := congrArg (ρ g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

private theorem fifthRoot_add {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (a b : ZMod 5) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add]

private theorem fifthRoot_sub_mul {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (a b : ZMod 5) :
    ζ ^ (b - a).val * ζ ^ a.val = ζ ^ b.val := by
  rw [← fifthRoot_add hζ, sub_add_cancel]

/-- The inverse normalizer carries each actual weight space to its rotated space. -/
theorem inverse_rotation_mapsTo (ρ : Representation E Carrier U)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (w : Weights.Weight) :
    Set.MapsTo (ρ TraceGeometry.r⁻¹) (weightSpace ρ ζ w)
      (weightSpace ρ ζ (Weights.rotate w)) := by
  intro v hv
  obtain ⟨hx, hy⟩ := hv
  have hx := Module.End.mem_eigenspace_iff.mp hx
  have hy := Module.End.mem_eigenspace_iff.mp hy
  have hc (g : Carrier) : ρ TraceGeometry.r (ρ g (ρ TraceGeometry.r⁻¹ v)) =
      ρ (TraceGeometry.r * g * TraceGeometry.r⁻¹) v := by
    rw [map_mul, map_mul]
    rfl
  have hr : ρ TraceGeometry.r (ρ TraceGeometry.r⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  constructor <;> apply Module.End.mem_eigenspace_iff.mpr
  · change ρ TraceGeometry.x (ρ TraceGeometry.r⁻¹ v) = ζ ^ w.2.val • _
    apply action_injective ρ TraceGeometry.r
    rw [map_smul, hr, hc, TraceGeometry.r_conj_x]
    exact hy
  · change ρ TraceGeometry.y (ρ TraceGeometry.r⁻¹ v) = ζ ^ (w.2 - w.1).val • _
    apply action_injective ρ TraceGeometry.r
    rw [map_smul, hr, hc, TraceGeometry.r_conj_y]
    apply action_injective ρ TraceGeometry.x
    rw [map_smul, hx, smul_smul, fifthRoot_sub_mul hζ,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    exact hy

/-- A literal restricted action map realizing the weight rotation. -/
def inverseRotationMap (ρ : Representation E Carrier U)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (w : Weights.Weight) :
    weightSpace ρ ζ w →ₗ[E] weightSpace ρ ζ (Weights.rotate w) :=
  (ρ TraceGeometry.r⁻¹).restrict (fun _ hv => inverse_rotation_mapsTo ρ hζ w hv)

private theorem weightMultiplicity_le_rotate [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (w : Weights.Weight) :
    weightMultiplicity ρ ζ w ≤ weightMultiplicity ρ ζ (Weights.rotate w) := by
  apply LinearMap.finrank_le_finrank_of_injective (f := inverseRotationMap ρ hζ w)
  intro a b h
  apply Subtype.ext
  exact action_injective ρ TraceGeometry.r⁻¹ (congrArg Subtype.val h)

/-- Rotation preserves the dimensions of the actual simultaneous eigenspaces. -/
theorem weightMultiplicity_rotate [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (w : Weights.Weight) :
    weightMultiplicity ρ ζ (Weights.rotate w) = weightMultiplicity ρ ζ w := by
  let m := weightMultiplicity ρ ζ
  have hi (a) : m a ≤ m (Weights.rotate a) := weightMultiplicity_le_rotate ρ hζ a
  have h0 := hi w
  have h1 := hi (Weights.rotate w)
  have h2 := hi ((Weights.rotate^[2]) w)
  have h3 := hi ((Weights.rotate^[3]) w)
  have h4 := hi ((Weights.rotate^[4]) w)
  have h5 := hi ((Weights.rotate^[5]) w)
  have hsix : ∀ a, (Weights.rotate^[6]) a = a := by decide +kernel
  change m ((Weights.rotate^[5]) w) ≤ m ((Weights.rotate^[6]) w) at h5
  rw [hsix] at h5
  change m ((Weights.rotate^[2]) w) ≤ m ((Weights.rotate^[3]) w) at h2
  change m ((Weights.rotate^[3]) w) ≤ m ((Weights.rotate^[4]) w) at h3
  change m ((Weights.rotate^[4]) w) ≤ m ((Weights.rotate^[5]) w) at h4
  change m (Weights.rotate w) ≤ m ((Weights.rotate^[2]) w) at h1
  change m (Weights.rotate w) = m w
  omega

/-- All three inputs to the finite certificate hold for any faithful degree-six action. -/
theorem four_patterns [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ i : Fin 4, ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w := by
  apply four_patterns_of_weight_decomposition ρ ζ (weightMultiplicity_rotate ρ hζ)
  · exact (sum_weightMultiplicity ρ hζ).trans hdim
  · simpa only [hdim] using weightMultiplicity_zero_lt ρ hρ ζ


end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
