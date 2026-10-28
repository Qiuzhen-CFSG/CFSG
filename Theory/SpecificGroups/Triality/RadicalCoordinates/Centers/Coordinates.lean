module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.HighestRoot
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Pairing

/-!
# Scalar coordinates for the arms radical center calculation

Compose the published root-orbit, fixed-product and central-quotient
equivalences to retain the actual Geck marking. Define the collecting scalar
using Tr(a F(b)), whose Frobenius shift comes from the published root order.
Nondegeneracy proves that the radical of its alternating form is precisely
the highest-root coordinate. This scalar calculation is unconditional;
the matrix multiplication and commutator identities remain separate obligations.

Source: GLS3 2.4.5 and §2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section

noncomputable section
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates.Centers
open Parabolics

abbrev ArmsParameters (P : Parameters) := RootOrbitParameters P .arms

abbrev armsSubgroup (P : Parameters) := descendSubgroup P (rootSubgroup P .arms)

/-- The published faithful parametrization, restricted to the arms radical. -/
def armsEquiv (P : Parameters) (hp : P.prime = 2) :
    ArmsParameters P ≃ descendSubgroup P (rootSubgroup P .arms) :=
  (rootOrbitEquiv P .arms).trans
    ((fixedRootEquiv P hp .arms).trans (descendedRootEquiv P hp .arms).toEquiv)

/-- The same parameters, still in the split Geck matrix group. -/
def armsProduct (P : Parameters) (v : ArmsParameters P) : SplitGroup P :=
  orderedProduct P (expand P (extendOrbit P .arms v))

/-- Parameters supported only on the highest root. -/
def centralParameters (P : Parameters) (z : fixedField P) : ArmsParameters P :=
  (0, ![0, 0, z])

theorem armsProduct_centralParameters (P : Parameters) (z : fixedField P) :
    armsProduct P (centralParameters P z) = curve P 11 z.val := by
  simp [armsProduct, centralParameters, orderedProduct, expand, extendOrbit,
    List.ofFn_succ, -fieldFrobenius_apply]

theorem armsEquiv_centralParameters (P : Parameters) (hp : P.prime = 2)
    (z : fixedField P) :
    (armsEquiv P hp (centralParameters P z)).val = highestHom P hp (Multiplicative.ofAdd z) := by
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  exact armsProduct_centralParameters P z

theorem armsEquiv_central_eq_one_iff (P : Parameters) (hp : P.prime = 2)
    (z : fixedField P) : armsEquiv P hp (centralParameters P z) = 1 ↔ z = 0 := by
  constructor
  · intro h
    have hh : highestHom P hp (Multiplicative.ofAdd z) = highestHom P hp 1 := by
      calc
        highestHom P hp (Multiplicative.ofAdd z) =
            (armsEquiv P hp (centralParameters P z)).val :=
          (armsEquiv_centralParameters P hp z).symm
        _ = 1 := congrArg (fun u : armsSubgroup P => u.val) h
        _ = highestHom P hp 1 := (map_one _).symm
    exact congrArg Multiplicative.toAdd (highestHom_injective P hp hh)
  · intro h
    subst z
    apply Subtype.ext
    exact (armsEquiv_centralParameters P hp 0).trans (map_one (highestHom P hp))

/-- The scalar correction expected on collecting a product in the published
root order. Its occurrence in the actual matrix product is a separate theorem. -/
def armsCocycle (P : Parameters) (v w : ArmsParameters P) : fixedField P :=
  v.2 1 * w.2 0 + armsPairing P (w.1 0) (v.1 1)

def armsMultiply (P : Parameters) (v w : ArmsParameters P) : ArmsParameters P :=
  (v.1 + w.1, ![v.2 0 + w.2 0, v.2 1 + w.2 1, v.2 2 + w.2 2 + armsCocycle P v w])

/-- Alternating scalar obtained by antisymmetrizing the collecting cocycle
in characteristic two; no group commutator identity is assumed here. -/
def armsCommutator (P : Parameters) (v w : ArmsParameters P) : fixedField P :=
  armsCocycle P v w + armsCocycle P w v

@[simp] theorem armsCommutator_central_left (P : Parameters) (z : fixedField P)
    (v : ArmsParameters P) : armsCommutator P (centralParameters P z) v = 0 := by
  simp [armsCommutator, armsCocycle, centralParameters]

@[simp] theorem armsCommutator_central_right (P : Parameters) (v : ArmsParameters P)
    (z : fixedField P) : armsCommutator P v (centralParameters P z) = 0 := by
  simp [armsCommutator, armsCocycle, centralParameters]

/-- The radical of the explicit alternating scalar is exactly the last
coordinate. This is a field calculation, prior to identifying it with the
commutator of the Geck products. -/
theorem armsCommutator_radical (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) (h : ∀ w, armsCommutator P v w = 0) :
    v = centralParameters P (v.2 2) := by
  have hd : v.2 1 = 0 := by
    simpa [armsCommutator, armsCocycle] using h (0, ![1, 0, 0])
  have hc : v.2 0 = 0 := by
    simpa [armsCommutator, armsCocycle] using h (0, ![0, 1, 0])
  have ha : v.1 0 = 0 := armsPairing_left_nondegenerate P hp _ (fun x => by
    simpa [armsCommutator, armsCocycle] using h (![0, x], 0))
  have hb : v.1 1 = 0 := armsPairing_right_nondegenerate P hp _ (fun x => by
    simpa [armsCommutator, armsCocycle] using h (![x, 0], 0))
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [centralParameters, ha, hb]
  · funext i
    fin_cases i <;> simp [centralParameters, hc, hd]

theorem armsCommutator_radical_iff (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) :
    (∀ w, armsCommutator P v w = 0) ↔ v = centralParameters P (v.2 2) := by
  constructor
  · exact armsCommutator_radical P hp v
  · intro h w
    rw [h]
    exact armsCommutator_central_left P _ w

/-- The two singleton root groups already attain every commutator scalar. -/
theorem armsCommutator_singletons (P : Parameters) (z : fixedField P) :
    armsCommutator P (0, ![0, z, 0]) (0, ![1, 0, 0]) = z := by
  simp [armsCommutator, armsCocycle]

theorem armsMultiply_self (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P) :
    armsMultiply P v v = centralParameters P (armsCocycle P v v) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply Prod.ext
  · funext i
    exact CharTwo.add_self_eq_zero (v.1 i)
  · funext i
    fin_cases i <;> simp [armsMultiply, centralParameters, CharTwo.add_self_eq_zero]

end Triality.Standard.RadicalCoordinates.Centers
