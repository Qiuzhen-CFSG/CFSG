module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Frattini
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.Index

public import Theory.GroupTheory.FrattiniFlagQuotientPair

/-!
# The actual PSU₅(4) Sylow group and its two automorphism quotients

The literal projective flag unipotents have order 2²⁰. The existing
isotropic-parabolic bound excludes 2²¹ from the special-unitary order;
the projective surjection therefore makes the flag subgroup's ambient
index odd. This constructs an actual projective Sylow two-subgroup.

Sylow conjugacy transports its involution-defined Frattini flag to every
Sylow subgroup of an equivalent group. Each flag factor has order sixteen,
so the two induced automorphism quotients have orders avoiding 25 and a
solvable common kernel. This discharges the concrete Sylow marking and
section-action premises in the unitary-five case of Aschbacher--Smith
4.4.10--11, printed p.621. The matrices are those of F.1.12(7),
printed pp.263--264.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.Flag
open PlaneCore
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

/-- The concrete flag subgroup has the full defining-characteristic order. -/
theorem unipotent_card_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Nat.card (unipotent J c hc hJ) = 2 ^ 20 := by
  rw [← Nat.card_congr (coordinatesEquivUnipotent J c hc hJ).toEquiv]
  change Nat.card (Parameters J ⋊[Parameters.planeAction.comp
    (SpecialLinearGroup.upperUnipotentHom F)] Multiplicative F) = _
  rw [SemidirectProduct.card, parameters_card J hcard hconj]
  change 2 ^ 16 * Nat.card F = _
  rw [hcard]
  norm_num

/-- The flag unipotents embedded in the actual projective unitary group. -/
def ambientUnipotent (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (unipotent J c hc hJ).map (planeParabolic J).subtype

/-- The inclusion into the ambient group preserves the literal coordinates. -/
noncomputable def unipotentEquivAmbient (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : unipotent J c hc hJ ≃* ambientUnipotent J c hc hJ :=
  (unipotent J c hc hJ).equivMapOfInjective _ (planeParabolic J).subtype_injective

/-- The established ambient two-part makes this actual subgroup Sylow. -/
theorem ambientUnipotent_index_odd (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    ¬ 2 ∣ (ambientUnipotent J c hc hJ).index := by
  have hU : Nat.card (ambientUnipotent J c hc hJ) = 2 ^ 20 :=
    (Nat.card_congr (unipotentEquivAmbient J c hc hJ).symm.toEquiv).trans
      (unipotent_card_four J hcard hconj c hc hJ)
  intro hi
  have hd := Nat.mul_dvd_mul hU.symm.dvd hi
  rw [(ambientUnipotent J c hc hJ).card_mul_index, ← pow_succ] at hd
  exact HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.not_dvd_special_card
    J hcard hconj hJ
      (hd.trans (Subgroup.card_dvd_of_surjective (project J) (project_surjective J)))

/-- The literal flag subgroup as a Sylow subgroup of PSU₅(4). -/
def unipotentSylowFour (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  ((unipotent_isPGroup J c hc hJ).map (planeParabolic J).subtype).toSylow
    (ambientUnipotent_index_odd J hcard hconj c hc hJ)

/-- Explicit semidirect-product coordinates for the actual Sylow subgroup. -/
noncomputable def unipotentSylowFourEquivCoordinates (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    unipotentSylowFour J hcard hconj c hc hJ ≃* Coordinates J :=
  (unipotentEquivAmbient J c hc hJ).symm.trans
    (coordinatesEquivUnipotent J c hc hJ).symm

/-- Every Sylow subgroup in this projective model inherits the two intrinsic
order-sixteen Frattini sections. -/
theorem sylow_invariant_frattini_flag_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G) :
    ∃ Q : Subgroup (P ⧸ frattini P),
      (∀ a : MulAut P, Q.map (quotientAut (frattini P) a).toMonoidHom = Q) ∧
      Nat.card Q = 16 ∧ Nat.card ((P ⧸ frattini P) ⧸ Q) = 16 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨c, hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let e₁ : P ≃* R := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  let e₂ := R.equiv (unipotentSylowFour J hcard hconj c hc hJ)
  let e₃ := unipotentSylowFourEquivCoordinates J hcard hconj c hc hJ
  simpa only [hcard] using invariant_frattini_flag_of_equiv J c hc hJ
    (e₁.trans (e₂.trans e₃))

/-- The intrinsic Sylow automorphism condition supplied by the actual
unitary-five model and its preserved Frattini flag. -/
theorem sylow_solvableQuotientPair_four (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G) :
    Theory.GroupTheory.HasSolvableQuotientPair 25 (MulAut P) := by
  obtain ⟨Q, hQ, hcardQ, hcardquot⟩ :=
    sylow_invariant_frattini_flag_four J hcard hconj hJ e P
  exact Theory.GroupTheory.hasSolvableQuotientPair25_of_invariant_frattini_flag
    P.isPGroup' Q hQ hcardQ hcardquot

end Theory.SpecificGroups.UnitaryFive.Flag
