module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.PointTests

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementTests.Obstructions

/-!
# Soundness of the Rudvalis local centralizer certificates

Two point images determine an element of the fixed local subgroup. Thus
coordinate conjugacy and commutation checks give identities on the original
model. A noncommuting pair in a representative's centralizer, with its first
element square-one, refutes the centrality hypothesis. Conjugation inside
`localP` transports this hypothesis along the literal centralizer intersection.

The nonsquare branch reuses the elementary catalogue's checked point witnesses.
The actual finite checks and their application are in `Sieve.Certificate` and
`Sieve`. Source motivation and ATLAS provenance: `Sieve/source/README.md`,
GLS3 Table 5.3r and pp.291–292. These local criteria are not quoted book theorems.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers.Sieve
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate
set_option maxRecDepth 30000
set_option Elab.async false

/-- The literal centrality premise of `RepresentativeCover`. -/
@[expose] public def CentralSquares (i : Model) : Prop :=
 ∀ x ∈ centralizerAt i, x ^ 2 = 1 → x ∈ centralizer (centralizerAt i : Set Model)

/-- Sixteen candidate class representatives, with the identity first. -/
@[expose] public def classIndex : Fin 16 → Fin 16384 :=
 ![0, 2, 8, 13, 37, 64, 128, 158, 211, 390, 600, 768, 1536, 3008, 4096, 12288]

/-- Either a previously certified nonsquare or a two-point conjugacy check. -/
@[expose] public def RowCheck (n : Fin 16384) (r : Fin 16) (g : Fin 16384) : Prop :=
 ElementChecks.witness n % 4 = 1 ∨
 (normalFormPermutation n (normalFormPermutation g 0) =
    normalFormPermutation g (normalFormPermutation (classIndex r) 0) ∧
  normalFormPermutation n (normalFormPermutation g 1) =
    normalFormPermutation g (normalFormPermutation (classIndex r) 1))
public instance (n : Fin 16384) (r : Fin 16) (g : Fin 16384) : Decidable (RowCheck n r g) :=
 inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

public theorem row_sound (n : Fin 16384) (r : Fin 16) (g : Fin 16384)
 (h : RowCheck n r g) (hsq : normalForm n ^ 2 = 1) :
 normalForm n = MulAut.conj (normalForm g) (normalForm (classIndex r)) := by
  rcases h with h | h
  · have hc := ElementChecks.checked n
    have hn : ElementChecks.witness n % 4 ≠ 0 := by omega
    simp only [ElementChecks.RowCheck, if_neg hn, if_pos h] at hc
    apply False.elim
    apply hc
    have he := congrArg modelSubgroup.subtype hsq
    change modelSubgroup.subtype (normalForm n) ^ 2 = 1 at he
    rw [← normalFormPermutation_eq] at he
    exact congrArg (fun q : Equiv.Perm (Fin 4060) => q (ElementChecks.witnessPoint n)) he
  · change normalForm n = normalForm g * normalForm (classIndex r) * (normalForm g)⁻¹
    apply (eq_mul_inv_iff_mul_eq).2
    apply eq_of_two_points
      (localP.mul_mem (normalForm_mem n) (normalForm_mem g))
      (localP.mul_mem (normalForm_mem g) (normalForm_mem (classIndex r)))
    · change modelSubgroup.subtype (normalForm n) (modelSubgroup.subtype (normalForm g) 0) =
        modelSubgroup.subtype (normalForm g) (modelSubgroup.subtype (normalForm (classIndex r)) 0)
      simpa only [← normalFormPermutation_eq] using h.1
    · change modelSubgroup.subtype (normalForm n) (modelSubgroup.subtype (normalForm g) 1) =
        modelSubgroup.subtype (normalForm g) (modelSubgroup.subtype (normalForm (classIndex r)) 1)
      simpa only [← normalFormPermutation_eq] using h.2

public theorem centralSquares_of_conj (g : Model) (hg : g ∈ localP) (i : Model)
 (h : CentralSquares (MulAut.conj g i)) : CentralSquares i := by
  let a := MulAut.conj g
  have hm (x : Model) (hx : x ∈ centralizerAt i) : a x ∈ centralizerAt (a i) := by
   rw [← map_centralizerAt g hg i]
   exact mem_map.mpr ⟨x, hx, rfl⟩
  intro x hx hs
  apply mem_centralizer_iff.mpr
  intro y hy
  apply a.injective
  simpa only [map_mul] using
   mem_centralizer_iff.mp (h (a x) (hm x hx) (by simpa using congrArg a hs)) (a y) (hm y hy)

@[expose] public def CommuteCheck (x y : Fin 16384) : Prop :=
 normalFormPermutation x (normalFormPermutation y 0) =
  normalFormPermutation y (normalFormPermutation x 0) ∧
 normalFormPermutation x (normalFormPermutation y 1) =
  normalFormPermutation y (normalFormPermutation x 1)
public instance (x y : Fin 16384) : Decidable (CommuteCheck x y) :=
 inferInstanceAs (Decidable (_ ∧ _))

private theorem commute_sound (x y : Fin 16384) (h : CommuteCheck x y) :
 Commute (normalForm x) (normalForm y) := by
  apply commute_of_two_points (normalForm_mem x) (normalForm_mem y)
  · simpa only [← normalFormPermutation_eq] using h.1
  · simpa only [← normalFormPermutation_eq] using h.2

/-- Two centralizer elements, the first square-one, which fail to commute. -/
@[expose] public def BadCheck (r : Fin 16) (x y : Fin 16384) : Prop :=
 CommuteCheck x (classIndex r) ∧ CommuteCheck y (classIndex r) ∧
 (normalFormPermutation x (normalFormPermutation x 0) = 0 ∧
  normalFormPermutation x (normalFormPermutation x 1) = 1) ∧
 (normalFormPermutation x (normalFormPermutation y 0) ≠
   normalFormPermutation y (normalFormPermutation x 0) ∨
  normalFormPermutation x (normalFormPermutation y 1) ≠
   normalFormPermutation y (normalFormPermutation x 1))
public instance (r : Fin 16) (x y : Fin 16384) : Decidable (BadCheck r x y) :=
 inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∧ _) ∧ (_ ∨ _)))

public theorem bad_sound (r : Fin 16) (x y : Fin 16384) (h : BadCheck r x y) :
 ¬ CentralSquares (normalForm (classIndex r)) := by
  intro hc
  have hx : normalForm x ∈ centralizerAt (normalForm (classIndex r)) :=
   ⟨normalForm_mem x, mem_centralizer_singleton_iff.mpr (commute_sound _ _ h.1).eq⟩
  have hy : normalForm y ∈ centralizerAt (normalForm (classIndex r)) :=
   ⟨normalForm_mem y, mem_centralizer_singleton_iff.mpr (commute_sound _ _ h.2.1).eq⟩
  have hs : normalForm x ^ 2 = 1 := by
   apply square_eq_one_of_two_points (normalForm_mem x)
   · simpa only [← normalFormPermutation_eq] using h.2.2.1.1
   · simpa only [← normalFormPermutation_eq] using h.2.2.1.2
  have he := (mem_centralizer_iff.mp (hc _ hx hs) _ hy).symm
  have hp (p : Fin 4060) :
    normalFormPermutation x (normalFormPermutation y p) =
    normalFormPermutation y (normalFormPermutation x p) := by
   have he' := congrArg modelSubgroup.subtype he
   change modelSubgroup.subtype (normalForm x) * modelSubgroup.subtype (normalForm y) =
     modelSubgroup.subtype (normalForm y) * modelSubgroup.subtype (normalForm x) at he'
   rw [← normalFormPermutation_eq, ← normalFormPermutation_eq] at he'
   exact congrArg (fun q : Equiv.Perm (Fin 4060) => q p) he'
  exact h.2.2.2.elim (fun h => h (hp 0)) (fun h => h (hp 1))

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers.Sieve
