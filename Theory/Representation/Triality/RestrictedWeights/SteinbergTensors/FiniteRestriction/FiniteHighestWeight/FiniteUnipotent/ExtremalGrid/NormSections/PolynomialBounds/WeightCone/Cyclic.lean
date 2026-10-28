module

public import Theory.AlgebraicGroup.Borel.OppositeBigCell
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight

/-!
# Cyclic highest vectors and a dense Borel product

A subspace containing a cyclic highest vector and stable under the opposite
Borel is the whole representation. A functional annihilating the subspace
has a regular matrix coefficient vanishing on the big cell, hence everywhere.
Cyclicity then makes the functional zero. No irreducibility is needed.

Source: the big-cell argument of GLS3 §1.14 and Steinberg,
*Representations of algebraic groups* (1963), §2.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
open Theory.AlgebraicGroup
open scoped Pointwise
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] in
/-- Inversion interchanges the two actual Borel products and preserves density. -/
theorem reverse_product_dense {T : ClosedSubgroup K} {D : RootGroupData K T}
    {P : Set D.Root} (H : OppositeBorelBigCell T D P) :
    Dense ((H.data.Bopp.toSubgroup : Set (Variety.Point K)) *
      (H.data.B.toSubgroup : Set (Variety.Point K))) := by
  let e : Variety.Point K ≃ₜ Variety.Point K :=
    { toFun := fun g => g⁻¹
      invFun := fun g => g⁻¹
      left_inv := inv_inv
      right_inv := inv_inv
      continuous_toFun := (Theory.AlgebraicGroup.invMorphism K).continuous
      continuous_invFun := (Theory.AlgebraicGroup.invMorphism K).continuous }
  apply (H.product_dense.preimage e.isOpenMap).mono
  intro x hx
  obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_mul.mp hx
  change b * c = x⁻¹ at hbc
  have h : x = c⁻¹ * b⁻¹ := by rw [← inv_inv x, ← hbc, mul_inv_rev]
  rw [h]
  exact Set.mul_mem_mul (H.data.Bopp.inv_mem hc) (H.data.B.inv_mem hb)

private theorem coefficient_zero_of_dense
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (l : Module.Dual k V) (v : V) {Z : Set (Variety.Point K)}
    (hZ : Dense Z) (h : ∀ g ∈ Z, l ((rho.action g).1 v) = 0) :
    ∀ g, l ((rho.action g).1 v) = 0 := by
  obtain ⟨e, f, hf⟩ := hrho
  let q := rationalRepresentationLinearMatrixCoefficient rho e f l v
  have hq (g) : q g = l ((rho.action g).1 v) :=
    rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l v g
  have hc : IsClosed {g : Variety.Point K | q g = 0} := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    obtain ⟨p, hp⟩ := q.representedBy
    refine ⟨{p}, ?_⟩
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rw [← hp g]
  have hsub : Z ⊆ {g : Variety.Point K | q g = 0} := by
    intro g hg
    rw [Set.mem_ofPred_eq, hq]
    exact h g hg
  intro g
  rw [← hq]
  exact closure_minimal hsub hc (hZ g)

/-- Dense-product cyclicity criterion, with the actual acting subgroups.
The second subgroup preserves the highest line; the first preserves the
candidate subspace. -/
theorem submodule_eq_top_of_dense_product
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (B C : ClosedSubgroup K)
    (hdense : Dense ((C.toSubgroup : Set (Variety.Point K)) *
      (B.toSubgroup : Set (Variety.Point K))))
    (v : V) (hv : GeneratesInvariantLine rho B v)
    (hcyc : IsCyclicRepresentation rho v)
    (W : Submodule k V) (hvW : v ∈ W)
    (hW : ∀ g ∈ C, ∀ w ∈ W, (rho.action g).1 w ∈ W) : W = ⊤ := by
  by_contra hne
  obtain ⟨l, hl, hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  have hz : ∀ g, l ((rho.action g).1 v) = 0 := by
    apply coefficient_zero_of_dense rho hrho l v hdense
    intro g hg
    obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp hg
    obtain ⟨d, hd⟩ := hv.2 b hb
    rw [map_mul]
    change l ((rho.action c).1 ((rho.action b).1 v)) = 0
    rw [hd, map_smul, map_smul, hker (hW c hc v hvW), smul_zero]
  let A : Submodule k V := ⨅ g : Variety.Point K, LinearMap.ker (l.comp (rho.action g).1)
  have hA : IsInvariantSubmodule rho A := by
    intro g x hx
    rw [Submodule.mem_iInf] at hx ⊢
    intro t
    have ht := hx (t * g)
    change l ((rho.action t).1 ((rho.action g).1 x)) = 0
    simpa [map_mul] using ht
  have hvA : v ∈ A := by rw [Submodule.mem_iInf]; exact hz
  have htop := hcyc A hA hvA
  apply hl
  ext x
  have hx : x ∈ A := htop ▸ Submodule.mem_top
  rw [Submodule.mem_iInf] at hx
  simpa using hx 1

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
