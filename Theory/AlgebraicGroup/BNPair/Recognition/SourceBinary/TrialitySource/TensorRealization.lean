module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorForm
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorCoordinates

/-!
# Faithful coordinates on the original cubic module

Embed the original module into its Schur-field extension by v ↦ 1 ⊗ v,
then apply the constructed tensor equivalence. Faithful flatness makes
this additive realization injective, and the original action is retained.
An additive root fixed by the upper unipotents therefore lies on the
highest tensor axis; its Weyl conjugate lies on the opposite axis with
exactly the same additive coefficient. The literal quotient application
in TensorRootAxes proves those stabilizer inputs from structural roots.

Source: Fong--Seitz II, the source-basis comparison on printed pp.218--219.
The middle-root coordinates and scalar compatibility are further steps.
-/

@[expose] public noncomputable section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL2.BinarySmall
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorRealization
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
local notation "E" => Module.End (ZMod 2)[SL(2,F)] ρ.asModule
local notation "C" => AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)

/-- The original module embeds faithfully in its constructed tensor model.
The action equation uses the original vectors, before any basis choice. -/
theorem exists_realization (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n)) :
    ∃ κ : F →+* C, ∃ J : V →+ TripleSpace C,
      Function.Injective J ∧ ∀ (g : SL(2,F)) (v : V),
        J (ρ g v) = TensorAction.cubicTensor κ σ g (J v) := by
  obtain ⟨κ,⟨φ⟩⟩ := TensorAction.recognition ρ hnt hn hF hV σ hσ
  let J : V →+ TripleSpace C := {
    toFun v := φ (1 ⊗ₜ[E] ρ.asModuleEquiv.symm v)
    map_zero' := by simp only [map_zero,TensorProduct.tmul_zero]
    map_add' a b := by simp only [map_add,TensorProduct.tmul_add] }
  refine ⟨κ,J,?_,?_⟩
  · exact φ.toLinearEquiv.injective.comp
      ((Module.FaithfullyFlat.tensorProduct_mk_injective (A := E) (B := C) ρ.asModule).comp
        ρ.asModuleEquiv.symm.injective)
  · intro g v
    have ht : φ (extendScalars C ρ.endFieldRep g (1 ⊗ₜ[E] ρ.asModuleEquiv.symm v)) =
        TensorAction.cubicTensor κ σ g (φ (1 ⊗ₜ[E] ρ.asModuleEquiv.symm v)) :=
      LinearMap.congr_fun (φ.isIntertwining' g) _
    change φ (1 ⊗ₜ[E] ρ.asModuleEquiv.symm (ρ g v)) =
      TensorAction.cubicTensor κ σ g (φ (1 ⊗ₜ[E] ρ.asModuleEquiv.symm v))
    simpa only [extendScalars_apply,
      LinearMap.baseChange_tmul,endFieldRep_apply,LinearEquiv.apply_symm_apply] using ht

section Axes
variable {C' A : Type*} [Field C'] [AddCommGroup A]
  (κ : F →+* C') (σ : F ≃+* F) (J : V →+ TripleSpace C')
  (hJ : ∀ (g : SL(2,F)) (v : V), J (ρ g v) = TensorAction.cubicTensor κ σ g (J v))
  (hcube : ∀ a,σ (σ (σ a)) = a) (hne : ∃ a,σ a ≠ a)
  (b : A →+ V) (hfix : ∀ a t, ρ (uni t) (ρ (weyl F) (b a)) = ρ (weyl F) (b a))

include hJ hcube hne hfix in
omit [Finite F] [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible] in
/-- The same additive coefficient describes both extreme source axes.
Only the upper stabilizer and the literal Weyl action are used. -/
theorem extreme_axes : ∃ c : A →+ C',
    (∀ a, J (ρ (weyl F) (b a)) = c a • TensorCoordinates.basis ((0,0),0)) ∧
    (∀ a, J (b a) = c a • TensorCoordinates.basis ((1,1),1)) := by
  let c : A →+ C' := {
    toFun a := TensorCoordinates.coordinates (J (ρ (weyl F) (b a))) ((0,0),0)
    map_zero' := by simp
    map_add' a d := by simp }
  have he (a : A) : J (ρ (weyl F) (b a)) = c a • TensorCoordinates.basis ((0,0),0) := by
    obtain ⟨u,hu⟩ := (TensorCoordinates.upper_fixed_iff κ σ hcube hne _).mp (by
      intro t
      rw [← hJ,hfix])
    have hc : c a = u := by
      change TensorCoordinates.coordinates (J (ρ (weyl F) (b a))) ((0,0),0) = u
      rw [hu]
      simp [TensorCoordinates.coordinates]
    exact hc.symm ▸ hu
  refine ⟨c,he,?_⟩
  intro a
  have hw : ρ (weyl F) (ρ (weyl F) (b a)) = b a := by
    rw [← Module.End.mul_apply,← map_mul,weyl_sq,map_one,Module.End.one_apply]
  rw [← hw,hJ,he,map_smul,TensorCoordinates.weyl_top]

end Axes

/-- Construct the faithful tensor realization together with both extreme
root axes from a faithful additive root and its upper stabilizer. -/
theorem exists_axes (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n))
    (hcube : ∀ a,σ (σ (σ a)) = a) (hne : ∃ a,σ a ≠ a)
    {A : Type*} [AddCommGroup A] (b : A →+ V) (hb : Function.Injective b)
    (hfix : ∀ a t,ρ (uni t) (ρ (weyl F) (b a)) = ρ (weyl F) (b a)) :
    ∃ κ : F →+* C, ∃ J : V →+ TripleSpace C, ∃ c : A →+ C,
      Function.Injective J ∧ Function.Injective c ∧
      (∀ (g : SL(2,F)) v,J (ρ g v) = TensorAction.cubicTensor κ σ g (J v)) ∧
      (∀ a,J (ρ (weyl F) (b a)) = c a • TensorCoordinates.basis ((0,0),0)) ∧
      (∀ a,J (b a) = c a • TensorCoordinates.basis ((1,1),1)) := by
  obtain ⟨κ,J,hJ,hact⟩ := exists_realization ρ hnt hn hF hV σ hσ
  obtain ⟨c,hE,hB⟩ := extreme_axes ρ κ σ J hact hcube hne b hfix
  refine ⟨κ,J,c,hJ,?_,hact,hE,hB⟩
  intro a d had
  apply hb
  apply hJ
  rw [hB,hB,had]

/-- Normalize both extreme axes simultaneously at the source parameter one.
The new coefficient remains additive and faithful; multiplicativity has
not been assumed. -/
theorem exists_normalized_axes (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n))
    (hcube : ∀ a,σ (σ (σ a)) = a) (hne : ∃ a,σ a ≠ a)
    {K : Type*} [Field K] (b : K →+ V) (hb : Function.Injective b)
    (hfix : ∀ a t,ρ (uni t) (ρ (weyl F) (b a)) = ρ (weyl F) (b a)) :
    ∃ κ : F →+* C, ∃ J : V →+ TripleSpace C, ∃ c : K →+ C,
      Function.Injective J ∧ Function.Injective c ∧ c 1 = 1 ∧
      (∀ (g : SL(2,F)) v,J (ρ g v) = TensorAction.cubicTensor κ σ g (J v)) ∧
      (∀ a,J (ρ (weyl F) (b a)) = c a • TensorCoordinates.basis ((0,0),0)) ∧
      (∀ a,J (b a) = c a • TensorCoordinates.basis ((1,1),1)) := by
  obtain ⟨κ,J,c,hJ,hc,hact,hE,hB⟩ := exists_axes ρ hnt hn hF hV σ hσ hcube hne b hb hfix
  have hc1 : c 1 ≠ 0 := by
    intro he
    exact one_ne_zero (hc (he.trans c.map_zero.symm))
  let J' : V →+ TripleSpace C := {
    toFun v := (c 1)⁻¹ • J v
    map_zero' := by simp
    map_add' v w := by simp [smul_add] }
  let c' : K →+ C := {
    toFun a := (c 1)⁻¹*c a
    map_zero' := by simp
    map_add' a d := by simp [mul_add] }
  refine ⟨κ,J',c',?_,?_,?_,?_,?_,?_⟩
  · exact (smul_right_injective (TripleSpace C) (inv_ne_zero hc1)).comp hJ
  · intro a d had
    exact hc (mul_left_cancel₀ (inv_ne_zero hc1) had)
  · exact inv_mul_cancel₀ hc1
  · intro g v
    change (c 1)⁻¹ • J (ρ g v) = TensorAction.cubicTensor κ σ g ((c 1)⁻¹ • J v)
    rw [hact,map_smul]
  · intro a
    change (c 1)⁻¹ • J (ρ (weyl F) (b a)) = ((c 1)⁻¹*c a) • _
    rw [hE,smul_smul]
  · intro a
    change (c 1)⁻¹ • J (b a) = ((c 1)⁻¹*c a) • _
    rw [hB,smul_smul]

/-- A constructed tensor chart with two normalized extreme root axes.
This finite interface keeps the source quotient's representation instances
out of the local coordinate calculations. -/
structure NormalizedAxes (σ : F ≃+* F) {K : Type*} [Field K] (b : K →+ V) where
  embedding : F →+* C
  chart : V →+ TripleSpace C
  coefficient : K →+ C
  chart_injective : Function.Injective chart
  coefficient_injective : Function.Injective coefficient
  coefficient_one : coefficient 1 = 1
  action : ∀ (g : SL(2,F)) v, chart (ρ g v) = TensorAction.cubicTensor embedding σ g (chart v)
  top : ∀ a,chart (ρ (weyl F) (b a)) = coefficient a • TensorCoordinates.basis ((0,0),0)
  bottom : ∀ a,chart (b a) = coefficient a • TensorCoordinates.basis ((1,1),1)

/-- Choose the chart proved above; no representation or axis equation is
required as an input beyond the original root stabilizer. -/
def normalizedAxes (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n))
    (hcube : ∀ a,σ (σ (σ a)) = a) (hne : ∃ a,σ a ≠ a)
    {K : Type*} [Field K] (b : K →+ V) (hb : Function.Injective b)
    (hfix : ∀ a t,ρ (uni t) (ρ (weyl F) (b a)) = ρ (weyl F) (b a)) :
    NormalizedAxes ρ σ b := Classical.choice (by
  obtain ⟨κ,J,c,hJ,hc,hc1,hact,hE,hB⟩ :=
    exists_normalized_axes ρ hnt hn hF hV σ hσ hcube hne b hb hfix
  exact ⟨⟨κ,J,c,hJ,hc,hc1,hact,hE,hB⟩⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorRealization
