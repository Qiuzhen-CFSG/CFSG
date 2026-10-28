module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Elements
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FieldTransport

/-!
# Transport of the concrete finite group data to the canonical model

An actual field isomorphism carries the concrete F₂₅ group entrywise to the
canonical group. It preserves precisely the literal upper-root-and-full-torus
Borel. The conditional certificate below discharges all arithmetic and transport
fields; its two remaining premises are coset separation and full generation
for the explicitly specified finite-group elements.

Source motivation: Guralnick–Malle Proposition 4.3, p.10, and
Aschbacher–Smith K.2, p.453.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A genuine field isomorphism to the literal canonical matrix field. -/
def fieldEquiv : Field ≃+* MatrixField := by
  letI : Fintype MatrixField := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, F25.card]
    exact (GaloisField.card 5 2 (by decide)).symm)

theorem fieldEquiv_conj (x : Field) :
    fieldEquiv (fieldForm.conj x) = modelForm.conj (fieldEquiv x) := by
  change fieldEquiv (F25.conjugation x) = _
  rw [F25.conjugation_eq_fifth, modelForm_conj, map_pow]

/-- Entrywise identification of the actual special-unitary groups. -/
def canonicalEquiv : standardGroup fieldForm ≃* standardGroup modelForm :=
  standardFieldEquiv fieldForm modelForm fieldEquiv fieldEquiv_conj

theorem canonicalEquiv_borel (g : standardGroup fieldForm) :
    canonicalEquiv g ∈ standardBorel modelForm ↔ g ∈ standardBorel fieldForm :=
  standardFieldEquiv_borel_iff fieldForm modelForm fieldEquiv fieldEquiv_conj g

theorem canonicalEquiv_entry (g : standardGroup fieldForm) (i j : Fin 3) :
    (canonicalEquiv g).val.val i j = fieldEquiv (g.val.val i j) :=
  standardFieldEquiv_entry fieldForm modelForm fieldEquiv fieldEquiv_conj g i j

/-- The primitive parameter in the literal canonical matrix field. -/
def canonicalParameter : MatrixFieldˣ := Units.map fieldEquiv.toMonoidHom parameter

theorem canonicalParameter_generates (k : MatrixFieldˣ) :
    k ∈ Subgroup.zpowers canonicalParameter := by
  let e := Units.mapEquiv fieldEquiv.toMulEquiv
  obtain ⟨l, rfl⟩ := e.surjective k
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (parameter_generates l)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  exact (map_zpow e parameter n).symm.trans (congrArg e hn)

/-- Entrywise transport of the checked root coordinates. -/
def canonicalRoot (a : Fin 2) (i : Fin 126) :
    hermitianUnipotentCoord (FormTransport.standardForm modelForm) :=
  ⟨(fieldEquiv (root a i).val.1, fieldEquiv (root a i).val.2), by
    change fieldEquiv (root a i).val.2 + modelForm.conj (fieldEquiv (root a i).val.2) +
      fieldEquiv (root a i).val.1 * modelForm.conj (fieldEquiv (root a i).val.1) = 0
    rw [← fieldEquiv_conj, ← fieldEquiv_conj, ← map_mul, ← map_add, ← map_add,
      ← map_zero fieldEquiv]
    exact congrArg fieldEquiv (root a i).property⟩

theorem canonicalEquiv_root (a : Fin 2) (i : Fin 126) :
    canonicalEquiv (principalRootIn fieldForm (root a i) : standardGroup fieldForm) =
      (principalRootIn modelForm (canonicalRoot a i) : standardGroup modelForm) := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  rw [canonicalEquiv_entry]
  change fieldEquiv (hermitianUnipotentMatrix _ (root a i) r c) =
    hermitianUnipotentMatrix _ (canonicalRoot a i) r c
  fin_cases r <;> fin_cases c <;>
    simp [hermitianUnipotentMatrix, canonicalRoot, FormTransport.standardForm_conj,
      fieldEquiv_conj]

theorem canonicalEquiv_torus (k : Fieldˣ) :
    canonicalEquiv (principalTorusIn fieldForm k : standardGroup fieldForm) =
      (principalTorusIn modelForm (Units.map fieldEquiv.toMonoidHom k) :
        standardGroup modelForm) := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  rw [canonicalEquiv_entry]
  change fieldEquiv (hermitianTorusMatrix _ k r c) =
    hermitianTorusMatrix _ (Units.map fieldEquiv.toMonoidHom k) r c
  fin_cases r <;> fin_cases c <;>
    simp [hermitianTorusMatrix, FormTransport.standardForm_conj, fieldEquiv_conj]

/-- Assemble the canonical certificate from the two remaining geometric facts.
Both premises refer to the fixed explicit elements, not arbitrary witnesses. -/
def certificate
    (hsep : ∀ i j, representative i * (representative j)⁻¹ ∈ standardBorel fieldForm → i = j)
    (hgen : Subgroup.closure (Set.range generator) = ⊤) : GroupCertificate where
  parameter := canonicalParameter
  parameter_generates := canonicalParameter_generates
  representative i := canonicalEquiv (representative i)
  generator a := canonicalEquiv (generator a)
  separates i j h := hsep i j ((canonicalEquiv_borel _).mp (by
    simpa only [map_mul, map_inv] using h))
  generates := by
    have h := congrArg (fun H : Subgroup (standardGroup fieldForm) =>
      H.map canonicalEquiv.toMonoidHom) hgen
    rw [MonoidHom.map_closure,
      Subgroup.map_top_of_surjective canonicalEquiv.toMonoidHom canonicalEquiv.surjective] at h
    simpa only [← Set.range_comp, Function.comp_def, MulEquiv.coe_toMonoidHom] using h
  root := canonicalRoot
  exponent := exponent
  transition a i := by
    have h := congrArg canonicalEquiv (transition a i)
    simp only [map_mul, Subgroup.coe_mul, canonicalEquiv_root, canonicalEquiv_torus] at h
    simpa only [canonicalParameter, map_pow, Subgroup.coe_mul, Subgroup.coe_pow] using h
  coefficient := coefficient

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
