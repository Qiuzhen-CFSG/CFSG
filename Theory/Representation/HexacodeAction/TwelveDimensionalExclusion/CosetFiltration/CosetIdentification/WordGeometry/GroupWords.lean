module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.Certificates

/-!
# The original subgroup and transporter equations in the actual cover

The eight positive subgroup words form a subgroup, and its equality with the
closure of all three original generators follows in both directions. Faithful
field matrices interpret the checked multiplication, inverse and transporter
equations as identities of actual cover elements. In particular every literal
inverse transporter is one of the eight words in that same subgroup.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
See `source/README.md` for witness provenance and ATLAS attribution.
-/

@[expose] public section

open Atlas.Codes
open Representation.Hexacode.SixDimensional.EvenImage.PairData
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry

/-- A word in the original three subgroup generators. -/
def subgroupWord (w : List (Fin 3)) : Cover :=
  (w.map fun a => evalWord (sylowWords a)).prod

def subgroupElement (p : Fin 8) : Cover := subgroupWord (subgroupWords p)

theorem coverMatrix_subgroupWord (w : List (Fin 3)) :
    coverMatrix (subgroupWord w) =
      decode ((w.map fun a => wordMatrix (sylowWords a)).foldr mm ident) := by
  induction w with
  | nil => simp [subgroupWord, decode_ident]
  | cons a w ih =>
    change coverMatrix (evalWord (sylowWords a) * subgroupWord w) = _
    rw [map_mul, coverMatrix_word, ih, ← decode_mm]
    rfl

theorem coverMatrix_subgroupElement (p : Fin 8) :
    coverMatrix (subgroupElement p) = decode (subgroupMatrix p) := by
  rw [subgroupElement, coverMatrix_subgroupWord, subgroup_checks]

theorem coverMatrix_representative (i : Fin 45) :
    coverMatrix (representative i) = decode (representativeMatrix i) := by
  rw [representative, coverMatrix_word, representative_checks]

theorem subgroupElement_mem (p : Fin 8) : subgroupElement p ∈ candidateSubgroup := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨a,rfl⟩

theorem subgroupElement_zero : subgroupElement 0 = 1 := rfl

theorem subgroupElement_mul (a b : Fin 8) :
    subgroupElement a * subgroupElement b = subgroupElement (subgroupMul a b) := by
  apply coverMatrix_injective
  rw [map_mul, coverMatrix_subgroupElement, coverMatrix_subgroupElement,
    coverMatrix_subgroupElement, ← decode_mm, subgroup_mul_checks]

theorem subgroupElement_inv (a : Fin 8) :
    (subgroupElement a)⁻¹ = subgroupElement (subgroupInv a) := by
  apply (eq_inv_of_mul_eq_one_left ?_).symm
  apply coverMatrix_injective
  rw [map_mul, coverMatrix_subgroupElement, coverMatrix_subgroupElement,
    ← decode_mm, subgroup_inv_checks, map_one, decode_ident]

/-- The eight displayed words form a subgroup of the literal cover. -/
def wordSubgroup : Subgroup Cover where
  carrier := Set.range subgroupElement
  one_mem' := ⟨0,subgroupElement_zero⟩
  mul_mem' := by
    rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨subgroupMul a b, (subgroupElement_mul a b).symm⟩
  inv_mem' := by
    rintro x ⟨a,rfl⟩
    exact ⟨subgroupInv a, (subgroupElement_inv a).symm⟩

theorem candidate_eq_wordSubgroup : candidateSubgroup = wordSubgroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a,rfl⟩
    let t : Fin 8 := (![1,2,3] : Fin 3 → Fin 8) a
    refine ⟨t, ?_⟩
    fin_cases a <;> change evalWord _ * 1 = _ <;> exact mul_one _
  · rintro x ⟨a,rfl⟩
    exact subgroupElement_mem a

theorem transporter_eq (j : Fin 2) (i : Fin 45) :
    inverseTransporter j i = subgroupElement (transporterIndex j i) := by
  have h : ((coverGenerator j)⁻¹ * representative i) *
      subgroupElement (transporterIndex j i) =
      hexEvenZ ^ (phase j i).val * representative (rowSource j i) := by
    apply coverMatrix_injective
    rw [map_mul, map_mul, show coverMatrix (coverGenerator j)⁻¹ =
      decode (letterMatrix (j,-1)) from by
        simpa only [zpow_neg_one] using coverMatrix_letter (j,-1),
      coverMatrix_representative, coverMatrix_subgroupElement, map_mul,
      map_pow, coverMatrix_scalar, coverMatrix_representative,
      ← decode_mpow, ← decode_mm, ← decode_mm, ← decode_mm,
      transporter_checks]
  rw [inverseTransporter, ← h, inv_mul_cancel_left]

/-- The actual cover product in each of the 1080 slots. -/
def productElement (a : ProductIndex) : Cover :=
  (hexEvenZ ^ a.1.2.val * representative a.1.1) * subgroupElement a.2

theorem coverMatrix_productElement (a : ProductIndex) :
    coverMatrix (productElement a) = decode (productMatrix a) := by
  rw [productElement, map_mul, map_mul, map_pow, coverMatrix_scalar,
    coverMatrix_representative, coverMatrix_subgroupElement, ← decode_mpow,
    ← decode_mm, ← decode_mm]
  rfl

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry
