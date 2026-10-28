module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.ActionData

/-!
# Coordinates on the literal max4 central quotient

The first eight shared words span the quotient, since the last three words
are the marked center. The quotient and coordinate space both have order 256,
so the resulting linear map is an equivalence. The three source-structure
premises remain explicit. CentralWordIdentities is a separate finite certificate,
not a structural or representation-theoretic assumption.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
open scoped IsMulCommutative
namespace Rudvalis.CoveringIncidence.Max4Steinberg

variable (hgen : closure (Set.range Max4Words.generator) = max4Core)

@[expose] public def coreWord (j : Fin 11) : max4Core :=
  ⟨Max4Words.generator j, hgen ▸ subset_closure ⟨j, rfl⟩⟩

@[expose] public def quotientWord (j : Fin 11) : Max4CentralQuotient :=
  QuotientGroup.mk' (center max4Core) (coreWord hgen j)

public theorem coreWord_closure : closure (Set.range (coreWord hgen)) = ⊤ := by
  apply map_injective max4Core.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact hgen

public theorem quotientWord_closure : closure (Set.range (quotientWord hgen)) = ⊤ := by
  have h := congrArg (fun H : Subgroup max4Core =>
    H.map (QuotientGroup.mk' (center max4Core))) (coreWord_closure hgen)
  rw [MonoidHom.map_closure, ← Set.range_comp, map_top_of_surjective _ (QuotientGroup.mk'_surjective (center max4Core))] at h
  exact h

public theorem quotientWord_central (hc : CentralWordIdentities)
    (j : Fin 11) (hj : 8 ≤ j.val) : quotientWord hgen j = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have he : j = ⟨8 + (j.val - 8), by omega⟩ := Fin.ext (by change j.val = 8 + (j.val - 8); omega)
  have hm : Max4Words.generator j ∈ max4CoreCenter := by
    rw [he, hc ⟨j.val - 8, by omega⟩]
    exact marked_eight_le_core_center (markedBasis _).property
  obtain ⟨x, hx, heq⟩ := mem_map.mp hm
  exact (show x = coreWord hgen j from Subtype.ext heq) ▸ hx

variable [IsElementaryAbelian 2 Max4CentralQuotient]

public noncomputable def quotientFromVector : Eight →ₗ[ZMod 2] Additive Max4CentralQuotient :=
  Fintype.linearCombination (ZMod 2)
    (fun i : Fin 8 => Additive.ofMul (quotientWord hgen ⟨i.val, by omega⟩))

public theorem quotientFromVector_single (i : Fin 8) :
    quotientFromVector hgen (Pi.single i 1) =
      Additive.ofMul (quotientWord hgen ⟨i.val, by omega⟩) := by
  simp [quotientFromVector, Fintype.linearCombination_apply_single]

public theorem quotientFromVector_surjective (hc : CentralWordIdentities) :
    Function.Surjective (quotientFromVector hgen) := by
  let f : Multiplicative Eight →* Max4CentralQuotient :=
    (quotientFromVector hgen).toAddMonoidHom.toMultiplicativeLeft
  have hr : f.range = ⊤ := by
    apply top_unique
    rw [← quotientWord_closure hgen]
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j.val < 8
    · exact ⟨Multiplicative.ofAdd (Pi.single ⟨j.val, hj⟩ 1),
        quotientFromVector_single hgen ⟨j.val, hj⟩⟩
    · rw [quotientWord_central hgen hc j (by omega)]
      exact f.range.one_mem
  exact MonoidHom.range_eq_top.mp hr

public noncomputable def quotientCoordinates
    (hcenter : max4CoreCenter = elementary 2) (hc : CentralWordIdentities) :
    Additive Max4CentralQuotient ≃ₗ[ZMod 2] Eight :=
  (LinearEquiv.ofBijective (quotientFromVector hgen)
    ((Nat.bijective_iff_surjective_and_card (quotientFromVector hgen)).mpr
      ⟨quotientFromVector_surjective hgen hc, by
        change Nat.card Eight = Nat.card Max4CentralQuotient
        rw [max4CentralQuotient_card_of_center_eq hcenter]
        simp⟩)).symm

public theorem quotientCoordinates_word
    (hcenter : max4CoreCenter = elementary 2) (hc : CentralWordIdentities) (i : Fin 8) :
    quotientCoordinates hgen hcenter hc
        (Additive.ofMul (quotientWord hgen ⟨i.val, by omega⟩)) = Pi.single i 1 := by
  apply (quotientCoordinates hgen hcenter hc).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (quotientFromVector_single hgen i).symm

/-- The candidate is an actual equivalence on the literal central quotient. -/
public noncomputable def quotientEquiv
    (hcenter : max4CoreCenter = elementary 2) (hc : CentralWordIdentities) :
    Max4CentralQuotient ≃* Multiplicative Steinberg :=
  (((quotientCoordinates hgen hcenter hc).trans intertwinerLinear).trans
    coordinates.symm).toAddEquiv.toMultiplicativeRight

public theorem quotientEquiv_word
    (hcenter : max4CoreCenter = elementary 2) (hc : CentralWordIdentities) (j : Fin 11) :
    (quotientEquiv hgen hcenter hc (quotientWord hgen j)).toAdd = wordImage j := by
  by_cases hj : j.val < 8
  · change coordinates.symm (intertwinerLinear (quotientCoordinates hgen hcenter hc
      (Additive.ofMul (quotientWord hgen j)))) = _
    rw [quotientCoordinates_word hgen hcenter hc ⟨j.val, hj⟩]
    rw [wordImage_eq, wordVector, dif_pos hj, intertwinerLinear_apply]
  · rw [quotientWord_central hgen hc j (by omega), map_one]
    simp [wordImage_eq, wordVector, hj]

end Rudvalis.CoveringIncidence.Max4Steinberg
