module

public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.ElementarySixtyFour
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Maps

/-!
# Native transitivity of one Rudvalis elementary sixty-four row

Two explicit native words normalize the first certified row.  Their actions on
its 64 labels, together with short orbit paths, give transitivity on the 63
nonidentity elements.  Every point-action identity is checked on the certified
five-point base, using `Rudvalis.eq_of_smul_first_five`.

Source: GLS3 Table 5.3r, printed p.279, and Aschbacher--Smith 4.4.3,
printed pp.622--623.  The displayed words are retained in the source witness
file `Sylow/source/witnesses.json`; the finite identities below are the proof.
-/

public noncomputable section
set_option Elab.async false
set_option maxRecDepth 30000
namespace Rudvalis.BinaryThreeModules.ElementarySixtyFour

open Rudvalis
open Subgroup
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[expose] public def normalizerWord6 : List (Fin 2) := [1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1]
@[expose] public def normalizerWord9 : List (Fin 2) := [1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,0,1,1,0,1,1,1,1,1,1,0,1,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1]
@[expose] public def normalizerLetter : Fin 2 → Model := ![a,b]
@[expose] public def normalizerLetterMap : Fin 2 → Fin 4060 → Fin 4060 :=
  ![Data.aMap, Data.bMap]
@[expose] public def normalizerMap6 (x : Fin 4060) : Fin 4060 :=
  evalWord normalizerLetterMap normalizerWord6 x
@[expose] public def normalizerMap9 (x : Fin 4060) : Fin 4060 :=
  evalWord normalizerLetterMap normalizerWord9 x
@[expose] public def normalizer6 : Model :=
  (normalizerWord6.map normalizerLetter).prod
@[expose] public def normalizer9 : Model :=
  (normalizerWord9.map normalizerLetter).prod

public theorem normalizer6_smul (x : Fin 4060) :
    normalizer6 • x = normalizerMap6 x := by
  exact prod_smul _ _ (by intro i x; fin_cases i <;> rfl) _ x

public theorem normalizer9_smul (x : Fin 4060) :
    normalizer9 • x = normalizerMap9 x := by
  exact prod_smul _ _ (by intro i x; fin_cases i <;> rfl) _ x

@[expose] public def normalizerAction6 : Fin 64 → Fin 64 := ![0,18,10,23,53,21,7,48,16,63,58,61,55,56,5,50,62,6,52,17,49,9,59,22,60,20,54,4,51,19,57,1,32,43,31,27,14,2,33,42,28,24,36,47,37,46,13,12,11,15,41,34,40,35,26,30,45,38,8,3,25,29,44,39]
@[expose] public def normalizerAction9 : Fin 64 → Fin 64 := ![0,11,5,12,52,23,28,35,21,57,46,51,62,36,30,41,1,56,17,53,26,34,13,47,19,50,6,63,15,40,24,37,58,16,54,22,4,59,7,55,2,44,3,32,45,27,33,29,9,60,10,48,61,18,49,20,42,25,38,31,8,43,14,39]

private theorem normalizer6_row_conj (c : Fin 64) :
    normalizer6 * candidateNormalForm (rowIndex 0 c) =
      candidateNormalForm (rowIndex 0 (normalizerAction6 c)) * normalizer6 := by
  apply Rudvalis.eq_of_smul_first_five
  intro i
  simp only [mul_smul, normalizer6_smul, normal_smul]
  change normalizerMap6 (normalMap (rowIndex 0 c) (i.castLE (by decide))) =
    normalMap (rowIndex 0 (normalizerAction6 c))
      (normalizerMap6 (i.castLE (by decide)))
  revert c i
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem normalizer9_row_conj (c : Fin 64) :
    normalizer9 * candidateNormalForm (rowIndex 0 c) =
      candidateNormalForm (rowIndex 0 (normalizerAction9 c)) * normalizer9 := by
  apply Rudvalis.eq_of_smul_first_five
  intro i
  simp only [mul_smul, normalizer9_smul, normal_smul]
  change normalizerMap9 (normalMap (rowIndex 0 c) (i.castLE (by decide))) =
    normalMap (rowIndex 0 (normalizerAction9 c))
      (normalizerMap9 (i.castLE (by decide)))
  revert c i
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem normalizerAction6_surjective : Function.Surjective normalizerAction6 := by
  decide +kernel

private theorem normalizerAction9_surjective : Function.Surjective normalizerAction9 := by
  decide +kernel

private theorem normalizer6_map_row :
    (row 0).map (MulAut.conj normalizer6).toMonoidHom = row 0 := by
  apply le_antisymm
  · apply (map_le_iff_le_comap).2
    apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    change (MulAut.conj normalizer6).toMonoidHom
      (candidateNormalForm (rowIndex 0 c)) ∈ row 0
    have h := normalizer6_row_conj c
    have hc : (MulAut.conj normalizer6).toMonoidHom
        (candidateNormalForm (rowIndex 0 c)) =
        candidateNormalForm (rowIndex 0 (normalizerAction6 c)) := by
      change normalizer6 * candidateNormalForm (rowIndex 0 c) * normalizer6⁻¹ = _
      have hh := congrArg (fun z : Model => z * normalizer6⁻¹) h
      simpa [mul_assoc] using hh
    rw [hc]
    exact subset_closure (Set.mem_range_self _)
  · apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    change candidateNormalForm (rowIndex 0 c) ∈ _
    obtain ⟨d,hd⟩ := normalizerAction6_surjective c
    have h := normalizer6_row_conj d
    have hc : (MulAut.conj normalizer6).toMonoidHom
        (candidateNormalForm (rowIndex 0 d)) =
        candidateNormalForm (rowIndex 0 c) := by
      change normalizer6 * candidateNormalForm (rowIndex 0 d) * normalizer6⁻¹ = _
      have hh := congrArg (fun z : Model => z * normalizer6⁻¹) h
      rw [hd] at hh
      simpa [mul_assoc] using hh
    rw [← hc]
    exact Subgroup.mem_map_of_mem (MulAut.conj normalizer6).toMonoidHom
      (subset_closure (Set.mem_range_self d))

private theorem normalizer9_map_row :
    (row 0).map (MulAut.conj normalizer9).toMonoidHom = row 0 := by
  apply le_antisymm
  · apply (map_le_iff_le_comap).2
    apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    change (MulAut.conj normalizer9).toMonoidHom
      (candidateNormalForm (rowIndex 0 c)) ∈ row 0
    have h := normalizer9_row_conj c
    have hc : (MulAut.conj normalizer9).toMonoidHom
        (candidateNormalForm (rowIndex 0 c)) =
        candidateNormalForm (rowIndex 0 (normalizerAction9 c)) := by
      change normalizer9 * candidateNormalForm (rowIndex 0 c) * normalizer9⁻¹ = _
      have hh := congrArg (fun z : Model => z * normalizer9⁻¹) h
      simpa [mul_assoc] using hh
    rw [hc]
    exact subset_closure (Set.mem_range_self _)
  · apply (closure_le _).2
    rintro x ⟨c,rfl⟩
    change candidateNormalForm (rowIndex 0 c) ∈ _
    obtain ⟨d,hd⟩ := normalizerAction9_surjective c
    have h := normalizer9_row_conj d
    have hc : (MulAut.conj normalizer9).toMonoidHom
        (candidateNormalForm (rowIndex 0 d)) =
        candidateNormalForm (rowIndex 0 c) := by
      change normalizer9 * candidateNormalForm (rowIndex 0 d) * normalizer9⁻¹ = _
      have hh := congrArg (fun z : Model => z * normalizer9⁻¹) h
      rw [hd] at hh
      simpa [mul_assoc] using hh
    rw [← hc]
    exact Subgroup.mem_map_of_mem (MulAut.conj normalizer9).toMonoidHom
      (subset_closure (Set.mem_range_self d))

@[expose] public def rowNormalizerGenerators : Fin 2 → Model := ![normalizer6,normalizer9]
@[expose] public def rowNormalizer : Subgroup Model :=
  Subgroup.closure (Set.range rowNormalizerGenerators)

public theorem rowNormalizer_le_normalizer :
    rowNormalizer ≤ normalizer (row 0 : Set Model) := by
  apply (closure_le _).2
  rintro g ⟨k,rfl⟩
  fin_cases k
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr normalizer6_map_row
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr normalizer9_map_row

@[expose] public def rowAction : Fin 2 → Fin 64 → Fin 64 :=
  ![normalizerAction6,normalizerAction9]

@[expose] public def pathAction : List (Fin 2) → Fin 64 → Fin 64
  | [], c => c
  | k :: ks, c => pathAction ks (rowAction k c)

@[expose] public def pathNormalizer : List (Fin 2) → Model
  | [] => 1
  | k :: ks => pathNormalizer ks * rowNormalizerGenerators k

private theorem rowNormalizerGenerators_conj (k : Fin 2) (c : Fin 64) :
    rowNormalizerGenerators k * candidateNormalForm (rowIndex 0 c) *
        (rowNormalizerGenerators k)⁻¹ =
      candidateNormalForm (rowIndex 0 (rowAction k c)) := by
  fin_cases k
  · have h := normalizer6_row_conj c
    have hh := congrArg (fun z : Model => z * normalizer6⁻¹) h
    simpa [rowNormalizerGenerators,rowAction,mul_assoc] using hh
  · have h := normalizer9_row_conj c
    have hh := congrArg (fun z : Model => z * normalizer9⁻¹) h
    simpa [rowNormalizerGenerators,rowAction,mul_assoc] using hh

public theorem pathNormalizer_conj (l : List (Fin 2)) (c : Fin 64) :
    pathNormalizer l * candidateNormalForm (rowIndex 0 c) *
        (pathNormalizer l)⁻¹ =
      candidateNormalForm (rowIndex 0 (pathAction l c)) := by
  induction l generalizing c with
  | nil => simp [pathNormalizer,pathAction]
  | cons k ks ih =>
    change (pathNormalizer ks * rowNormalizerGenerators k) *
      candidateNormalForm (rowIndex 0 c) *
      (pathNormalizer ks * rowNormalizerGenerators k)⁻¹ = _
    calc
      (pathNormalizer ks * rowNormalizerGenerators k) *
          candidateNormalForm (rowIndex 0 c) *
          (pathNormalizer ks * rowNormalizerGenerators k)⁻¹ =
        pathNormalizer ks *
          (rowNormalizerGenerators k * candidateNormalForm (rowIndex 0 c) *
            (rowNormalizerGenerators k)⁻¹) * (pathNormalizer ks)⁻¹ := by group
      _ = pathNormalizer ks * candidateNormalForm (rowIndex 0 (rowAction k c)) *
          (pathNormalizer ks)⁻¹ := by rw [rowNormalizerGenerators_conj]
      _ = candidateNormalForm (rowIndex 0 (pathAction ks (rowAction k c))) :=
        ih (rowAction k c)

public theorem pathNormalizer_mem (l : List (Fin 2)) :
    pathNormalizer l ∈ rowNormalizer := by
  induction l with
  | nil => exact rowNormalizer.one_mem
  | cons k ks ih =>
    exact rowNormalizer.mul_mem ih
      (Subgroup.subset_closure (Set.mem_range_self k))

@[expose] public def pathWitness : Fin 64 → List (Fin 2) :=
  ![[],[1, 0, 0, 1],[1, 0, 0, 0, 0, 0, 0],[1, 1, 1, 1, 1, 0, 0],[1, 1, 1, 1, 0, 0],[1, 0, 0, 0, 1, 0],[1, 0, 0, 1, 0, 1, 0],[1, 1, 1],[1, 0],[1, 0, 1, 0],[1, 0, 0, 0, 0, 0, 0, 0],[1, 0, 0, 1, 1],[1, 1, 0, 0, 0, 0],[1, 1, 1, 1, 1, 1],[1, 0, 0, 0, 1],[1, 0, 1, 1, 1, 1, 0],[1, 0, 0],[1, 0, 0, 1, 0, 1],[1, 0, 0, 1, 0],[1, 1, 0, 0, 0, 1, 0],[1, 0, 1, 0, 1, 1, 0],[1, 0, 1],[1, 1, 1, 1, 1],[1, 0, 0, 0, 1, 0, 1],[1, 0, 0, 0, 1, 1, 1],[1, 0, 1, 0, 1, 1],[1, 0, 1, 1, 1, 0],[1, 1, 1, 1, 0],[1, 0, 0, 1, 0, 0, 0, 0],[1, 1, 0, 0, 0, 1],[1, 0, 0, 0, 1, 1],[1, 0, 1, 1, 0],[],[1, 1, 0],[1, 0, 1, 1],[1, 1, 1, 1],[1, 1, 1, 1, 1, 1, 1],[1, 0, 0, 0, 0, 0],[1, 1],[1, 0, 1, 0, 0, 0],[1, 0, 0, 1, 0, 0, 0],[1, 0, 1, 0, 1, 1, 1, 0],[1, 0, 1, 0, 0, 0, 0],[1, 1, 0, 0],[1, 0, 0, 0, 0],[1, 0, 0, 0, 0, 1],[1, 0, 0, 0, 0, 1, 0],[1, 1, 0, 0, 0],[1, 1, 1, 0],[1, 0, 1, 1, 1, 1],[1, 0, 1, 0, 1, 1, 1],[1, 0, 0, 1, 1, 1],[1, 0, 0, 1, 0, 0],[1, 1, 1, 1, 0, 0, 0],[1, 0, 1, 1, 1],[1, 0, 1, 0, 0, 0, 1],[1, 0, 0, 1, 0, 1, 1],[1, 0, 1, 0, 1],[1],[1, 1, 1, 1, 1, 0],[1, 0, 1, 1, 1, 1, 1],[1, 0, 0, 1, 1, 0],[1, 0, 0, 0],[1, 0, 1, 0, 0]]

public theorem pathWitness_reaches (c : Fin 64) (hc : c ≠ 0) :
    pathAction (pathWitness c) 32 = c := by
  revert c
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem rowIndex_zero_injective : Function.Injective (rowIndex 0) := by
  intro c d h
  revert c d
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private def rowElement (c : Fin 64) : row 0 :=
  ⟨candidateNormalForm (rowIndex 0 c), subset_closure (Set.mem_range_self c)⟩

private theorem rowElement_injective : Function.Injective rowElement := by
  intro c d h
  apply rowIndex_zero_injective
  apply normalForm_injective
  exact congrArg Subtype.val h

private theorem rowElement_zero : rowElement 0 = 1 := by
  apply Subtype.ext
  change candidateNormalForm (rowIndex 0 0) = 1
  rw [show rowIndex 0 0 = 0 by decide +kernel]
  apply Subtype.ext
  simp [candidateNormalForm]

/-- The two native words act transitively on the nonidentity elements of row 0.
The cardinality premise lets the 64 displayed generators exhaust the row. -/
public theorem row0_transitive_of_card (hcard : Nat.card (row 0) = 64) :
    ∀ x y : row 0, x ≠ 1 → y ≠ 1 →
      ∃ p : normalizer (row 0 : Set Model),
        p.val * x.val * p.val⁻¹ = y.val := by
  have hs : Function.Surjective rowElement :=
    (rowElement_injective.bijective_of_nat_card_le (by rw [Nat.card_fin,hcard])).2
  intro x y hx hy
  obtain ⟨c,rfl⟩ := hs x
  obtain ⟨d,rfl⟩ := hs y
  have hc : c ≠ 0 := by
    intro h
    apply hx
    rw [← rowElement_zero]
    rw [h]
  have hd : d ≠ 0 := by
    intro h
    apply hy
    rw [← rowElement_zero]
    rw [h]
  let pc := pathNormalizer (pathWitness c)
  let pd := pathNormalizer (pathWitness d)
  have hpc : pc * candidateNormalForm (rowIndex 0 32) * pc⁻¹ =
      candidateNormalForm (rowIndex 0 c) := by
    dsimp [pc]
    rw [pathNormalizer_conj, pathWitness_reaches c hc]
  have hpd : pd * candidateNormalForm (rowIndex 0 32) * pd⁻¹ =
      candidateNormalForm (rowIndex 0 d) := by
    dsimp [pd]
    rw [pathNormalizer_conj, pathWitness_reaches d hd]
  let p : Model := pd * pc⁻¹
  have hp : p ∈ normalizer (row 0 : Set Model) := by
    apply rowNormalizer_le_normalizer
    change pd * pc⁻¹ ∈ rowNormalizer
    exact rowNormalizer.mul_mem (pathNormalizer_mem _) (rowNormalizer.inv_mem (pathNormalizer_mem _))
  refine ⟨⟨p,hp⟩, ?_⟩
  change p * candidateNormalForm (rowIndex 0 c) * p⁻¹ =
    candidateNormalForm (rowIndex 0 d)
  dsimp [p]
  calc
    (pd * pc⁻¹) * candidateNormalForm (rowIndex 0 c) *
        (pd * pc⁻¹)⁻¹ =
      (pd * pc⁻¹) * (pc * candidateNormalForm (rowIndex 0 32) * pc⁻¹) *
        (pd * pc⁻¹)⁻¹ := by rw [hpc]
    _ = pd * candidateNormalForm (rowIndex 0 32) * pd⁻¹ := by group
    _ = candidateNormalForm (rowIndex 0 d) := hpd

end Rudvalis.BinaryThreeModules.ElementarySixtyFour
