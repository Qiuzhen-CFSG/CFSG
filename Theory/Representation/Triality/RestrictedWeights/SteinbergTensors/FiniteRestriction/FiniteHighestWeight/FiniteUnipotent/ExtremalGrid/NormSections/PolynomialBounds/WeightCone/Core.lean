module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Roots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.Cyclic

/-!
# Character cones and actual torus inversion

The cone is the monoid of products of nonnegative powers of the four simple
characters. Its associated subspace is the sum of precisely the allowed
weight spaces. Independence of weight spaces recovers character membership
when this subspace is the whole module. An actual ambient torus inverter
transports occurring characters to their inverses.

Source: GLS3 §1.14; Steinberg (1963), §2. All characters here are eigencharacters
of a left representation; direct simple-root characters are raw inverses.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
open Theory.AlgebraicGroup
open scoped BigOperators
universe u v
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- The nonnegative cone on four actual torus characters. -/
def characterCone (alpha : Fin 4 → TorusWeight T) : Submonoid (TorusWeight T) where
  carrier := {eta | ∃ c : Fin 4 → ℕ, eta = ∏ i, alpha i ^ c i}
  one_mem' := ⟨fun _ => 0, by simp⟩
  mul_mem' := by
    rintro eta theta ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨fun i => c i + d i, by simp [pow_add, Finset.prod_mul_distrib]⟩

theorem characterCone_generator (alpha : Fin 4 → TorusWeight T) (i : Fin 4) :
    alpha i ∈ characterCone alpha := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, ?_⟩
  simp

/-- Sum of the weight spaces below `chi` with differences in `M`. -/
def lowerSpace (rho : RationalRepresentation K V) (T : ClosedSubgroup K)
    (M : Submonoid (TorusWeight T)) (chi : TorusWeight T) : Submodule k V :=
  ⨆ mu ∈ {mu | chi * mu⁻¹ ∈ M}, weightSpace rho T mu

theorem weightSpace_le_lowerSpace (rho : RationalRepresentation K V)
    (M : Submonoid (TorusWeight T)) (chi mu : TorusWeight T)
    (hmu : chi * mu⁻¹ ∈ M) : weightSpace rho T mu ≤ lowerSpace rho T M chi :=
  le_iSup_of_le mu (le_iSup_of_le hmu le_rfl)

theorem highest_mem_lowerSpace (rho : RationalRepresentation K V)
    (M : Submonoid (TorusWeight T)) {chi : TorusWeight T} {v : V}
    (hv : IsWeightVector rho T v chi) : v ∈ lowerSpace rho T M chi :=
  weightSpace_le_lowerSpace rho M chi chi (by simp) hv.2

/-- Torus stability holds for any sum selected by a condition on characters. -/
theorem lowerSpace_torus_stable (rho : RationalRepresentation K V)
    (M : Submonoid (TorusWeight T)) (chi : TorusWeight T)
    (t : Variety.Point T.carrierVariety) {v : V} (hv : v ∈ lowerSpace rho T M chi) :
    (rho.action (T.includePoint t)).1 v ∈ lowerSpace rho T M chi := by
  refine Submodule.iSup_induction _ (motive := fun w =>
    (rho.action (T.includePoint t)).1 w ∈ lowerSpace rho T M chi) hv ?_ ?_ ?_
  · intro mu x hx
    refine Submodule.iSup_induction _ (motive := fun w =>
      (rho.action (T.includePoint t)).1 w ∈ lowerSpace rho T M chi) hx ?_ ?_ ?_
    · intro hmu y hy
      rw [hy t]
      exact (lowerSpace rho T M chi).smul_mem _
        (weightSpace_le_lowerSpace rho M chi mu hmu hy)
    · simp
    · intro y z hy hz
      simpa only [map_add] using (lowerSpace rho T M chi).add_mem hy hz
  · simp
  · intro y z hy hz
    simpa only [map_add] using (lowerSpace rho T M chi).add_mem hy hz

/-- Independence rules out any occurring character outside a spanning cone. -/
theorem weight_mem_of_lowerSpace_eq_top [FiniteDimensional k V] (rho : RationalRepresentation K V)
    (M : Submonoid (TorusWeight T)) (chi mu : TorusWeight T)
    (htop : lowerSpace rho T M chi = ⊤) (hmu : mu ∈ representationWeights rho T) :
    chi * mu⁻¹ ∈ M :=
  (weightSpace_iSupIndep rho T).mem_of_biSup_eq_top htop hmu

/-- The ambient point, not an abstract Weyl-group label, implements inversion. -/
def InvertsTorus (T : ClosedSubgroup K) (r : Variety.Point K) : Prop :=
  ∀ t : Variety.Point T.carrierVariety,
    r * T.includePoint t * r⁻¹ = (T.includePoint t)⁻¹

/-- Applying an actual torus inverter to a nonzero weight vector inverts its
character in the same representation. -/
theorem inverter_weightVector (rho : RationalRepresentation K V)
    (r : Variety.Point K) (hr : InvertsTorus T r)
    {mu : TorusWeight T} {v : V} (hv : IsWeightVector rho T v mu) :
    IsWeightVector rho T ((rho.action r).1 v) mu⁻¹ := by
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hv.1
    apply ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V) (rho.action r)).injective
    simpa using hzero
  · intro t
    have ht : T.includePoint t * r = r * T.includePoint t⁻¹ := by
      have h := hr t⁻¹
      change r * (T.includePoint t)⁻¹ * r⁻¹ = ((T.includePoint t)⁻¹)⁻¹ at h
      rw [inv_inv] at h
      calc
        T.includePoint t * r = (r * (T.includePoint t)⁻¹ * r⁻¹) * r := by rw [h]
        _ = r * T.includePoint t⁻¹ := by change _ = r * (T.includePoint t)⁻¹; group
    have he := congrArg (fun g => (rho.action g).1 v) ht
    simp only [map_mul, Units.val_mul, Module.End.mul_apply] at he
    rw [he, hv.2 t⁻¹, map_smul]
    have hc : mu.pointCharacter t⁻¹ = (mu⁻¹).pointCharacter t := by
      change (dPointEquiv 1 (mu.onPoints t⁻¹) 0 : k) =
        (dPointEquiv 1 (mu.onPoints t)⁻¹ 0 : k)
      rw [map_inv]
    rw [hc]

theorem inverter_weight_occurs (rho : RationalRepresentation K V)
    (r : Variety.Point K) (hr : InvertsTorus T r)
    {mu : TorusWeight T} (hmu : mu ∈ representationWeights rho T) :
    mu⁻¹ ∈ representationWeights rho T := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hmu
  have h := inverter_weightVector rho r hr ⟨hv0, hv⟩
  exact (Submodule.ne_bot_iff _).mpr ⟨_, h.2, h.1⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
