module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Coordinates
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Certificates
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.Rank
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.Marking

/-!
# Reduction of the marked four-space inspection to finite coverage

All fourteen listed matrices are excluded from a cubic-rank-one overgroup:
the checked words produce two independent commuting cubic elements in the
actual subgroup. The faithful bit action transfers these identities, and
the coordinate intertwiner identifies the literal deleted-permutation action.

`inspection_of_doubleCosetCoverage` assembles the requested universal
inspection from the remaining exhaustive double-coset coverage statement.
`actionImage_le_of_doubleCosetCoverage` applies it to the original component
and leaves the independently produced component rank bound explicit.
The exhaustive coverage statement is still a premise here.

Source: Aschbacher–Smith, proof of 8.2.8(1), printed p.719/PDF p.736;
H.4.6(2), printed p.382/PDF p.393, distinguishes this module from B/U.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
open Subgroup

private noncomputable def automorphismGenerator (r : MulAut Vector) : Fin 6 → MulAut Vector :=
  ![permutationAction cycleA, permutationAction cycleB, r,
    permutationAction cycleA⁻¹, permutationAction cycleB⁻¹, r⁻¹]

private noncomputable def automorphismWord (r : MulAut Vector) (w : List (Fin 6)) : MulAut Vector :=
  (w.map (automorphismGenerator r)).prod

private theorem bitAction_inverse (i : Fin 14) (r : MulAut Vector)
    (hr : bitAction r = applyMatrix (representative i)) :
    bitAction r⁻¹ = applyMatrix (representativeInverse i) := by
  have hh : bitAction r * (applyMatrix (representativeInverse i) : Function.End Bits) = 1 := by
    rw [hr]
    funext x
    exact representative_inverse i x
  have hi : bitAction r⁻¹ * bitAction r = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    bitAction r⁻¹ = bitAction r⁻¹ * 1 := (mul_one _).symm
    _ = bitAction r⁻¹ * (bitAction r * applyMatrix (representativeInverse i)) := by rw [hh]
    _ = applyMatrix (representativeInverse i) := by rw [← mul_assoc, hi, one_mul]

private theorem bitAction_word (i : Fin 14) (r : MulAut Vector)
    (hr : bitAction r = applyMatrix (representative i)) (w : List (Fin 6)) :
    bitAction (automorphismWord r w) = evaluateWord i w := by
  have hg (j : Fin 6) : bitAction (automorphismGenerator r j) = generator i j := by
    fin_cases j
    · exact bitAction_permutationAction cycleA
    · exact bitAction_permutationAction cycleB
    · exact hr
    · exact bitAction_permutationAction cycleA⁻¹
    · exact bitAction_permutationAction cycleB⁻¹
    · exact bitAction_inverse i r hr
  simp only [automorphismWord, evaluateWord, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun j _ => hg j)

private theorem word_mem (D : Subgroup (MulAut Vector))
    (hA : (alternatingGroup (Fin 5)).map permutationAction ≤ D)
    (r : MulAut Vector) (hr : r ∈ D) (w : List (Fin 6)) : automorphismWord r w ∈ D := by
  have ha : permutationAction cycleA ∈ D :=
    hA (mem_map.mpr ⟨cycleA, Equiv.Perm.mem_alternatingGroup.mpr cycles_even.1, rfl⟩)
  have hb : permutationAction cycleB ∈ D :=
    hA (mem_map.mpr ⟨cycleB, Equiv.Perm.mem_alternatingGroup.mpr cycles_even.2, rfl⟩)
  apply D.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  fin_cases j
  · exact ha
  · exact hb
  · exact hr
  · change permutationAction cycleA⁻¹ ∈ D
    rw [map_inv]
    exact D.inv_mem ha
  · change permutationAction cycleB⁻¹ ∈ D
    rw [map_inv]
    exact D.inv_mem hb
  · exact D.inv_mem hr

/-- Each listed representative forces an independent commuting cubic pair in
any overgroup of the marked alternating permutations. -/
theorem representative_forbidden (D : Subgroup (MulAut Vector))
    (hA : (alternatingGroup (Fin 5)).map permutationAction ≤ D)
    (hrank : primeRank 3 D ≤ 1) (i : Fin 14) (r : MulAut Vector) (hrD : r ∈ D)
    (hr : bitAction r = applyMatrix (representative i)) : False := by
  let a := permutationAction cycleA
  let b := automorphismWord r (witnessWord i)
  have haD : a ∈ D := hA ⟨cycleA, Equiv.Perm.mem_alternatingGroup.mpr cycles_even.1, rfl⟩
  have hbD : b ∈ D := word_mem D hA r hrD _
  have ha : bitAction a = permuteBits cycleA := bitAction_permutationAction _
  have hb : bitAction b = applyMatrix (witnessColumns i) :=
    (bitAction_word i r hr _).trans (witness_word i)
  have hp := witness_cubics i
  let f := bitAction.comp D.subtype
  have hf : Function.Injective f := bitAction_injective.comp D.subtype_injective
  have haf : f ⟨a, haD⟩ = permuteBits cycleA := ha
  have hbf : f ⟨b, hbD⟩ = applyMatrix (witnessColumns i) := hb
  apply cubic_pair_forbidden (⟨a, haD⟩ : D) (⟨b, hbD⟩ : D) _ _ _ _ _ _ _ hrank
  · apply hf
    simpa only [map_pow, map_one, haf] using hp.1
  · apply hf
    simpa only [map_pow, map_one, hbf] using hp.2.1
  · apply hf
    simpa only [map_mul, haf, hbf] using hp.2.2.1
  · intro h
    apply hp.2.2.2.1
    simpa only [haf, map_one] using congrArg f h
  · intro h
    apply hp.2.2.2.2.1
    simpa only [hbf, map_one] using congrArg f h
  · intro h
    apply hp.2.2.2.2.2.1
    simpa only [haf, hbf] using congrArg f h
  · intro h
    apply hp.2.2.2.2.2.2
    simpa only [haf, hbf, map_pow] using congrArg f h

/-- Exhaustive coverage is the only remaining finite input to the coordinate inspection. -/
theorem coordinate_inspection (coverage : DoubleCosetCoverage)
    (D : Subgroup (MulAut Vector))
    (hA : (alternatingGroup (Fin 5)).map permutationAction ≤ D)
    (hrank : primeRank 3 D ≤ 1) : D ≤ permutationAction.range := by
  intro f hf
  rcases coverage (columns f) (applyMatrix_columns_injective f) with
    ⟨σ, hσ⟩ | ⟨i, σ, τ, hσ, hτ, h⟩
  · refine ⟨σ, bitAction_injective ?_⟩
    rw [bitAction_permutationAction, bitAction_eq_applyMatrix, hσ]
  · have hσD : permutationAction σ ∈ D :=
      hA ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, rfl⟩
    have hτD : permutationAction τ ∈ D :=
      hA ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτ, rfl⟩
    let r := (permutationAction σ)⁻¹ * f * (permutationAction τ)⁻¹
    have hrD : r ∈ D := D.mul_mem (D.mul_mem (D.inv_mem hσD) hf) (D.inv_mem hτD)
    have hh : bitAction f = bitAction (permutationAction σ) *
        (applyMatrix (representative i) : Function.End Bits) * bitAction (permutationAction τ) := by
      rw [bitAction_eq_applyMatrix, bitAction_permutationAction, bitAction_permutationAction]
      exact h
    have hiσ : bitAction (permutationAction σ)⁻¹ * bitAction (permutationAction σ) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hiτ : bitAction (permutationAction τ) * bitAction (permutationAction τ)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hr : bitAction r = applyMatrix (representative i) := by
      simp only [r, map_mul, hh]
      calc
        _ = (bitAction (permutationAction σ)⁻¹ * bitAction (permutationAction σ)) *
            applyMatrix (representative i) *
            (bitAction (permutationAction τ) * bitAction (permutationAction τ)⁻¹) := by
              simp only [mul_assoc]
        _ = _ := by rw [hiσ, hiτ, one_mul, mul_one]
    exact False.elim (representative_forbidden D hA hrank i r hrD hr)

/-- Transport of the finite inspection to the literal marked module in `Marking`. -/
theorem inspection_of_doubleCosetCoverage (coverage : DoubleCosetCoverage) :
    CubicOvergroupInspection := by
  intro D hA hrank
  let e := MulAut.congr modelEquiv.symm
  let C := D.map e.toMonoidHom
  have hCA : (alternatingGroup (Fin 5)).map permutationAction ≤ C := by
    rintro a ⟨σ, hσ, rfl⟩
    exact ⟨BinaryPermutation.naturalMulAction (Fin 5) σ, hA ⟨σ, hσ, rfl⟩, rfl⟩
  have hCrank : primeRank 3 C ≤ 1 := by
    rw [← Theory.GroupTheory.primeRank_equiv 3 (D.equivMapOfInjective e.toMonoidHom e.injective)]
    exact hrank
  have hc := coordinate_inspection coverage C hCA hCrank
  intro f hf
  obtain ⟨σ, hσ⟩ := hc (show e f ∈ C from ⟨f, hf, rfl⟩)
  refine ⟨σ, e.injective ?_⟩
  exact hσ

/-- Application to the original component action; its independent rank bound
remains explicit. The coverage producer must still discharge `coverage`. -/
theorem actionImage_le_of_doubleCosetCoverage {G : Type*} [Group G] [Finite G]
    (L K U : Subgroup G) [Group.IsPerfect K] (coverage : DoubleCosetCoverage)
    (e : U ≃* FiveModule)
    (hmark : (actionImage (localResidual L U) U).map (MulAut.congr e).toMonoidHom =
      alternatingImage)
    (hRK : localResidual L U ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hrank : primeRank 3 K ≤ 1) :
    actionImage K U ≤ actionImage (localResidual L U) U :=
  actionImage_le_of_inspection L K U (inspection_of_doubleCosetCoverage coverage)
    e hmark hRK hKU hrank

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
