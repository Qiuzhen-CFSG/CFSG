module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.ModelActions
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions.Coordinates
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions.ScalarWeights
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions.FieldPairings

/-!
# The unitary Sylow-center action and its perfect-cover application

Choose a primitive unit of the coefficient field. Its inverse norm generates
the fixed-field units, and its first-coordinate scalar has order greater than
q + 1. The separated Frobenius weights therefore exclude every invariant binary
pairing. The coordinate results give center transitivity, a central derived
subgroup and the fixed-point-free action of this same actual torus parameter.
The field order supplies characteristic two and the odd period q² - 1; the
witness is the existing upper-root Sylow subgroup.

The final theorem discharges `UnitaryCenterActions` with every original model
guard retained. The unconditional covering application retains the original
covering map, kernel, model isomorphism and Sylow subgroup of the covering group.
The earlier conditional reductions remain available as separate public APIs.

Source: an alternative direct proof of the Sylow-center conclusion of GLS4,
Chapter 4, Lemma 2.8(c), using the matrix coordinates of Huppert II.10.12 and
the perfect central-cover criterion.
-/

public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
namespace BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions
variable {K : Type*} [Field K] (J : HermitianForm 3 K)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card K = (2^n)^2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2^n)

open OddPrimeSylow.NormalizedOuter.Coverage PerfectCentralCovering in
include hn hcard hfixed in
theorem root_action_of_field_pairings (k : Kˣ) (r : ℕ) (hodd : Odd r) (hkr : k ^ r = 1)
    (hknu : inverseNorm J k ≠ 1)
    (hfield : ∀ b : Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)),
      (∀ x y : Multiplicative K, b (.ofAdd ((torusWeight J k : K) * x.toAdd))
        (.ofAdd ((torusWeight J k : K) * y.toAdd)) = b x y) → b = 1) :
    SylowCenterAction (projectiveRoot J hJ) := by
  refine ⟨center_transitive J hJ hn hcard hfixed, Or.inr ⟨?_, torusNormalizer J hJ k,
    r, hodd, ?_, ?_, ?_⟩⟩
  · exact (root_commutator_eq_center J hJ hcard hfixed).le
  · rw [← map_pow, hkr, map_one]
  · exact center_fixed J hJ hn hcard hfixed k hknu
  · exact root_pairings_trivial J hJ hcard hfixed k hfield

open OddPrimeSylow.NormalizedOuter.Coverage PerfectCentralCovering in
omit [CharP K 2] in
include hJ hn hcard hfixed in
theorem exists_sylow_action_of_field_pairings (k : Kˣ) (hknu : inverseNorm J k ≠ 1)
    (hfield : ∀ b : Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)),
      (∀ x y : Multiplicative K, b (.ofAdd ((torusWeight J k : K) * x.toAdd))
        (.ofAdd ((torusWeight J k : K) * y.toAdd)) = b x y) → b = 1) :
    ∃ Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J), SylowCenterAction (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  refine ⟨EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed, ?_⟩
  obtain ⟨hodd, hkr⟩ := unit_odd_period hn hcard k
  exact root_action_of_field_pairings J hJ hn hcard hfixed k ((2^n)^2 - 1) hodd hkr hknu hfield

open OddPrimeSylow.NormalizedOuter.Coverage PerfectCentralCovering in
omit [CharP K 2] in
include hJ hn hcard hfixed in
theorem cover_center_of_field_pairings {E B : Type*} [Group E] [Finite E] [Group B]
    (f : Cover E B) (hker : Nat.card f.toMonoidHom.ker = 2)
    (e : B ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 E)
    (k : Kˣ) (hknu : inverseNorm J k ≠ 1)
    (hfield : ∀ b : Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)),
      (∀ x y : Multiplicative K, b (.ofAdd ((torusWeight J k : K) * x.toAdd))
        (.ofAdd ((torusWeight J k : K) * y.toAdd)) = b x y) → b = 1) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Q, hQ⟩ := exists_sylow_action_of_field_pairings J hJ hn hcard hfixed
    k hknu hfield
  exact f.sylow_center_eq_kernel_of_model_sylow hker e Q hQ P

open OddPrimeSylow.NormalizedOuter.Coverage PerfectCentralCovering in
omit [CharP K 2] in
include hJ hn hcard hfixed in
/-- A primitive torus parameter supplies every field of the action criterion
on the actual projective root Sylow. No scalar or pairing premise remains. -/
theorem exists_sylow_action :
    ∃ Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      SylowCenterAction (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hkorder : orderOf k = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hk, Nat.card_units]
  apply exists_sylow_action_of_field_pairings J hJ hn hcard hfixed k
    (primitive_inverseNorm_ne_one J hn hcard hfixed k hkorder)
  intro c hc
  exact field_pairings_trivial (2 * n) (by omega)
    (by simpa only [pow_mul, Nat.mul_comm] using hcard) (torusWeight J k : K)
    (primitive_weight_separated J hn hcard hfixed k hkorder) c hc

open PerfectCentralCovering in
omit [CharP K 2] in
include hJ hn hcard hfixed in
/-- The unitary model's proved action identifies the center of every covering
Sylow with the original double-cover kernel. -/
theorem cover_center {E B : Type*} [Group E] [Finite E] [Group B]
    (f : Cover E B) (hker : Nat.card f.toMonoidHom.ker = 2)
    (e : B ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 E) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Q, hQ⟩ := exists_sylow_action J hJ hn hcard hfixed
  exact f.sylow_center_eq_kernel_of_model_sylow hker e Q hQ P

end BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions

namespace BenderSuzuki.ZD.DirectSylowCenters

/-- The complete unitary normalizer-action contract, retaining the coefficient
field, stored standard form, both cardinalities and inherited simplicity. -/
theorem unitary_center_actions : UnitaryCenterActions := by
  intro K _ _ J _ n hn hJ hcard hfixed
  exact UnitaryActions.exists_sylow_action J hJ hn hcard hfixed

end BenderSuzuki.ZD.DirectSylowCenters
