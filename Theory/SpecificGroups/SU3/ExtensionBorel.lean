module
public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.ExtensionBorel.PGU
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.GroupTheory.AutomorphismExtensionBorel

/-!
# Borels in the actual diagonal and mixed extensions of PSU₃

The root normalizer in PGU is the image of upper triangular unitary matrices.
In any subgroup of the genuine unitary-semilinear automorphisms containing Inn,
the embedded root normalizer is the intersection with the concrete actor Borel.
The literal preimage of a mixed field–diagonal outer cyclic subgroup lies in
that semilinear group, without any splitting assumption. The final applications
retain the existing binary root Sylow and its original component embedding.

Source: Aschbacher–Smith, Notation A.3.16 and Lemma A.3.18, printed pp.51–52,
and case (iii) and the Borel placement in 13.6.6, printed p.927.

A.3.16 defines the nonsplit unitary extension as a graph-field fixed subgroup
of the linear extension. Its compatible identification with the mixed outer
preimage, and the whole-overgroup marking and Sylow alignment in Chapter 13,
remain with the source assembly owner. This module proves the intrinsic matrix
calculation for that realization, without asserting that identification.
-/

@[expose] public section
open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
open BorelTorus Theory.GroupTheory.AutomorphismExtensionBorel
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

include hJ in
/-- The inner map of the actual binary PSU carrier is injective. -/
theorem binary_inner_injective {m : ℕ} (hm : 1 < m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m)) :
    Function.Injective (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m
    (by omega) hcard hconj
  have hnonfixed : ∃ x : E, J.conj x ≠ x := by
    by_contra! h
    apply conj_ne_one_of_card J m (by omega) hcard hfixed
    exact RingEquiv.ext h
  exact MulAut.conj_injective_of_center_eq_bot
    (EvenTwoRank.standard_center_eq_bot J hJ hnonfixed)

/-- Every actual semilinear extension containing Inn has the same concrete
Borel, restricted to that extension. -/
theorem normalizer_semilinear_extension {m : ℕ} (hm : 1 < m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m))
    (H : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ H)
    (hsem : H ≤ semilinearGroup J hJ) :
    normalizer (rootIn (projectiveRoot J hJ) H : Set H) =
      (actorBorel J hJ).subgroupOf H := by
  apply normalizer_rootIn _ _ _ hinner (binary_inner_injective J hJ hm hcard hconj)
  intro a
  exact root_stabilizer_iff J hJ hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hcard hconj)
    a.val (hsem a.property)

/-- The literal mixed outer preimage of the specified field and unitary actors.
In the source application the unitary actor is diagonal. -/
def mixedPreimage (σ : E ≃+* E) (d : J.unitarySubgroup) :
    Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  outerPreimage (zpowers
    (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (fieldActor J hJ σ) *
      QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (J.unitaryConj d)))

/-- The literal mixed preimage contains all inner automorphisms. -/
theorem inner_le_mixedPreimage (σ : E ≃+* E) (d : J.unitarySubgroup) :
    MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ mixedPreimage J hJ σ d :=
  inner_le_outerPreimage _

/-- No splitting is needed to put the whole mixed preimage in the semilinear group. -/
theorem mixedPreimage_le_semilinear (σ : E ≃+* E) (d : J.unitarySubgroup) :
    mixedPreimage J hJ σ d ≤ semilinearGroup J hJ :=
  mixed_outerPreimage_le _ (inner_le_semilinear J hJ) _ _
    (field_mem_semilinear J hJ σ) (unitary_mem_semilinear J hJ d)

/-- Root-stabilizer input for the parent's literal outer-preimage alignment. -/
theorem mixed_root_stabilizer_iff {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (σ : E ≃+* E) (d : J.unitarySubgroup) (a : mixedPreimage J hJ σ d) :
    (projectiveRoot J hJ).map a.val.toMonoidHom = projectiveRoot J hJ ↔
      a.val ∈ actorBorel J hJ :=
  root_stabilizer_iff J hJ hcard hfixed a.val
    (mixedPreimage_le_semilinear J hJ σ d a.property)

/-- The exact mixed-preimage normalizer, retaining its natural inner embedding. -/
theorem normalizer_mixedPreimage {m : ℕ} (hm : 1 < m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m))
    (σ : E ≃+* E) (d : J.unitarySubgroup) :
    normalizer (rootIn (projectiveRoot J hJ) (mixedPreimage J hJ σ d) :
      Set (mixedPreimage J hJ σ d)) =
      (actorBorel J hJ).subgroupOf (mixedPreimage J hJ σ d) :=
  normalizer_semilinear_extension J hJ hm hcard hconj _
    (inner_le_mixedPreimage J hJ σ d) (mixedPreimage_le_semilinear J hJ σ d)

/-- The literal product of the chosen actors belongs to the mixed preimage. -/
theorem mixed_generator_mem (σ : E ≃+* E) (d : J.unitarySubgroup) :
    fieldActor J hJ σ * J.unitaryConj d ∈ mixedPreimage J hJ σ d := by
  change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
    (fieldActor J hJ σ * J.unitaryConj d) ∈ zpowers _
  rw [map_mul]
  exact mem_zpowers _

/-- For a diagonal unitary actor, the literal mixed generator is in the
computed Borel of its actual outer preimage. -/
theorem mixed_generator_mem_normalizer {m : ℕ} (hm : 1 < m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m))
    (σ : E ≃+* E) (d : J.unitarySubgroup)
    (hd : ∀ i j, i ≠ j → d.val.val i j = 0) :
    (⟨fieldActor J hJ σ * J.unitaryConj d, mixed_generator_mem J hJ σ d⟩ :
      mixedPreimage J hJ σ d) ∈
        normalizer (rootIn (projectiveRoot J hJ) (mixedPreimage J hJ σ d) :
          Set (mixedPreimage J hJ σ d)) := by
  rw [normalizer_mixedPreimage J hJ hm hcard hconj]
  change fieldActor J hJ σ * J.unitaryConj d ∈ actorBorel J hJ
  apply (actorBorel J hJ).mul_mem
  · exact Subgroup.mem_sup_right ⟨σ, rfl⟩
  · rw [← J.unitaryConjHom_apply]
    exact Subgroup.mem_sup_left ⟨d, (fun _ _ h => hd _ _ (ne_of_gt h)), rfl⟩

/-- The PGU calculation applied to the existing actual root Sylow subgroup. -/
theorem normalizer_pgu_rootSylow {m : ℕ} (hm : 1 < m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m)) :
    let P := EvenTwoRank.rootSylow J hJ (by omega : 0 < m) hcard
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hcard hconj)
    normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (componentInPGU J) : Set (projectiveUnitary J)) = pguBorel J := by
  exact normalizer_pguRoot J hJ hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hcard hconj)

/-- The source mixed-extension calculation at the genuine order-three actors.
The graph-field fixed-group identification of A.3.16 is a separate earlier
input: this theorem calculates the literal outer preimage and asserts no split
extension or identification with that fixed group. -/
theorem source_mixed_rootSylow_normalizer {m : ℕ} (hm : 1 < m)
    (_hthree : 3 ∣ m) (_hmod : 2 ^ m % 3 = 2)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ m))
    (σ : E ≃+* E) (_hfield : orderOf σ = 3)
    (d : J.unitarySubgroup) (_hdiagonal : ∀ i j, i ≠ j → d.val.val i j = 0)
    (_houter : orderOf
      (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (J.unitaryConj d)) = 3) :
    let P := EvenTwoRank.rootSylow J hJ (by omega : 0 < m) hcard
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hcard hconj)
    let H := mixedPreimage J hJ σ d
    normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (innerEmbedding H (inner_le_mixedPreimage J hJ σ d)) : Set H) =
        (actorBorel J hJ).subgroupOf H := by
  have h := normalizer_mixedPreimage J hJ hm hcard hconj σ d
  rw [rootIn_eq_map _ _ (inner_le_mixedPreimage J hJ σ d)] at h
  exact h

end BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
