module
public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech.Extension
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural

/-!
# The fixed signed natural module and the real Leech action

Evaluate a signed halfspace function at `(x,1)` and use the fixed coordinate
marking. This gives a linear equivalence taking `L¹(x)` to the standard
coordinate vector. The actual integral sign and permutation isometries
extend to the corresponding real coordinate maps by uniqueness of the Leech
extension. Checking the positive halfspace basis then proves intertwining
for the actual loop and standard-automorphism transports. The sign proof
uses `L⁰(x) = -L¹(x)`; a permutation sends the basis label forward while
its coordinate function is reindexed by the inverse.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.4, pp. 146–147, and the
natural-module identification and generator comparison on p. 148.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin
open SignedModules

/-- The fixed real comparison, using evaluation at the positive signed labels. -/
def naturalLeechComparison : Natural.B1_24 ≃ₗ[ℝ] NaturalSpace :=
  (Natural.coordinates 0).trans (LinearEquiv.funCongrLeft ℝ ℝ coordinateMarking)

@[simp] theorem naturalLeechComparison_apply (v : Natural.B1_24) (i : Fin 24) :
    naturalLeechComparison v i = v.val (coordinateMarking i, 1) := rfl

@[simp] theorem naturalLeechComparison_L_one (x : Omega) :
    naturalLeechComparison (Natural.L 0 1 x) =
      Pi.single (coordinateMarking.symm x) 1 := by
  ext i
  change Natural.coordinates 0 (Natural.L 0 1 x) (coordinateMarking i) = _
  rw [Natural.coordinates_L_one]
  by_cases h : i = coordinateMarking.symm x
  · subst i
    simp
  · have hm : coordinateMarking i ≠ x := by
      intro he
      exact h (coordinateMarking.injective (he.trans (coordinateMarking.apply_symm_apply x).symm))
    simp [h, hm]

/-- The actual real extension is the coordinate sign change. -/
theorem realLeechRepresentation_sign_apply (Y : golay) (v : NaturalSpace) (i : Fin 24) :
    realLeechRepresentation (signIsometry Y) v i =
      if Y.val (coordinateMarking i) = 0 then v i else -v i := by
  let f : NaturalSpace →ₗ[ℝ] NaturalSpace :=
    { toFun v i := if Y.val (coordinateMarking i) = 0 then v i else -v i
      map_add' v w := by ext i; dsimp; split <;> simp [add_comm]
      map_smul' r v := by ext i; dsimp; split <;> simp }
  have hf : f = (realLeechRepresentation (signIsometry Y)).toLinearMap := by
    apply realLeechRepresentation_unique
    intro x
    ext i
    change (if Y.val (coordinateMarking i) = 0 then
      (x.val (coordinateMarking i) : ℝ) / Real.sqrt 8 else
      -((x.val (coordinateMarking i) : ℝ) / Real.sqrt 8)) =
        ((if Y.val (coordinateMarking i) = 0 then x.val (coordinateMarking i)
          else -x.val (coordinateMarking i) : ℤ) : ℝ) / Real.sqrt 8
    split <;> simp [neg_div]
  exact congrArg (fun a : NaturalSpace →ₗ[ℝ] NaturalSpace => a v i) hf.symm

/-- The actual real extension uses inverse coordinate reindexing. -/
theorem realLeechRepresentation_permutation_apply (σ : Mathieu24CodeModel)
    (v : NaturalSpace) (i : Fin 24) :
    realLeechRepresentation (permutationEmbedding σ) v i =
      v (coordinateMarking.symm (σ.val.symm (coordinateMarking i))) := by
  let f : NaturalSpace →ₗ[ℝ] NaturalSpace :=
    { toFun v i := v (coordinateMarking.symm (σ.val.symm (coordinateMarking i)))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hf : f = (realLeechRepresentation (permutationEmbedding σ)).toLinearMap := by
    apply realLeechRepresentation_unique
    intro x
    ext i
    change (x.val (coordinateMarking (coordinateMarking.symm
      (σ.val.symm (coordinateMarking i)))) : ℝ) / Real.sqrt 8 =
        (x.val (σ.val.symm (coordinateMarking i)) : ℝ) / Real.sqrt 8
    rw [coordinateMarking.apply_symm_apply]
  exact congrArg (fun a : NaturalSpace →ₗ[ℝ] NaturalSpace => a v i) hf.symm

/-- A sign generator acts on each marked coordinate basis vector with the prescribed sign. -/
theorem realLeechRepresentation_sign_basis (Y : golay) (x : Omega) :
    realLeechRepresentation (signIsometry Y) (Pi.single (coordinateMarking.symm x) 1) =
      if Y.val x = 0 then Pi.single (coordinateMarking.symm x) 1
      else -Pi.single (coordinateMarking.symm x) 1 := by
  ext i
  rw [realLeechRepresentation_sign_apply]
  by_cases h : i = coordinateMarking.symm x
  · subst i
    simp only [coordinateMarking.apply_symm_apply]
    split <;> rfl
  · split_ifs <;> simp [h]

/-- The inverse coordinate action gives the forward permutation of basis labels. -/
theorem realLeechRepresentation_permutation_basis (σ : Mathieu24CodeModel) (x : Omega) :
    realLeechRepresentation (permutationEmbedding σ) (Pi.single (coordinateMarking.symm x) 1) =
      Pi.single (coordinateMarking.symm (σ.val x)) 1 := by
  ext i
  rw [realLeechRepresentation_permutation_apply]
  by_cases h : i = coordinateMarking.symm (σ.val x)
  · subst i
    simp
  · have hm : coordinateMarking.symm (σ.val.symm (coordinateMarking i)) ≠
        coordinateMarking.symm x := by
      intro he
      have hx := coordinateMarking.symm.injective he
      have hx' : coordinateMarking i = σ.val x := by
        rw [← hx, σ.val.apply_symm_apply]
      exact h (coordinateMarking.injective
        (hx'.trans (coordinateMarking.apply_symm_apply _).symm))
    simp [h, hm]

/-- The first loop generator fixes the first natural module. -/
theorem naturalLeechComparison_psi1 (d : ParkerLoop) (v : Natural.B1_24) :
    naturalLeechComparison (Natural.transport (psi1 d) (Natural.psi_carries 0 0 d) v) =
      naturalLeechComparison v := by
  have h : Natural.transport (psi1 d) (Natural.psi_carries 0 0 d) =
      LinearEquiv.refl ℝ Natural.B1_24 :=
    (Natural.transport_kernel_iff _ _).mpr (Natural.psi_self_halfspace 0 d)
  rw [h]
  rfl

/-- The genuine halfspace action of `ψ₂(d)` is the actual Golay sign isometry. -/
theorem naturalLeechComparison_psi2 (d : ParkerLoop) (v : Natural.B1_24) :
    naturalLeechComparison (Natural.transport (psi2 d) (Natural.psi_carries 1 0 d) v) =
      realLeechRepresentation (signIsometry d.1) (naturalLeechComparison v) := by
  have h : naturalLeechComparison.toLinearMap.comp
      (Natural.transport (psi2 d) (Natural.psi_carries 1 0 d)).toLinearMap =
      (realLeechRepresentation (signIsometry d.1)).toLinearMap.comp
        naturalLeechComparison.toLinearMap := by
    apply (Natural.basis 0).ext
    intro x
    rw [Natural.basis_eq_L]
    change naturalLeechComparison
      (Natural.transport (Natural.psiAt 1 d) (Natural.psi_carries 1 0 d)
        (Natural.L 0 1 x)) =
      realLeechRepresentation (signIsometry d.1) (naturalLeechComparison (Natural.L 0 1 x))
    rw [Natural.psi_linear 1 0, naturalLeechComparison_L_one, realLeechRepresentation_sign_basis]
    have hflip : Natural.L 0 0 x = -Natural.L 0 1 x := Natural.L_add_one 0 1 x
    rcases bit_cases (d.1.val x) with hd | hd <;> simp [hd, hflip]
  exact congrArg (fun f : Natural.B1_24 →ₗ[ℝ] NaturalSpace => f v) h

/-- The genuine standard action has forward basis labels and inverse coordinate reindexing. -/
theorem naturalLeechComparison_psiAut1 (α : ParkerStandardGroup) (v : Natural.B1_24) :
    naturalLeechComparison
      (Natural.transport (psiAut1 α.val) (Natural.standard_self_carries 0 α) v) =
      realLeechRepresentation (permutationEmbedding (parkerStandardProjection α))
        (naturalLeechComparison v) := by
  have h : naturalLeechComparison.toLinearMap.comp
      (Natural.transport (psiAut1 α.val) (Natural.standard_self_carries 0 α)).toLinearMap =
      (realLeechRepresentation (permutationEmbedding (parkerStandardProjection α))).toLinearMap.comp
        naturalLeechComparison.toLinearMap := by
    apply (Natural.basis 0).ext
    intro x
    rw [Natural.basis_eq_L]
    change naturalLeechComparison
      (Natural.transport (Natural.psiAutAt 0 α.val) (Natural.standard_self_carries 0 α)
        (Natural.L 0 1 x)) =
      realLeechRepresentation (permutationEmbedding (parkerStandardProjection α))
        (naturalLeechComparison (Natural.L 0 1 x))
    rw [Natural.standard_self_linear, naturalLeechComparison_L_one,
      naturalLeechComparison_L_one, realLeechRepresentation_permutation_basis]
  exact congrArg (fun f : Natural.B1_24 →ₗ[ℝ] NaturalSpace => f v) h

end Sporadic.Monster.Construction.LocalC
