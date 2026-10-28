module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five.Model
public import Theory.GroupTheory.PerfectCentralCoverTorusNormalizer
import all Theory.GroupTheory.PerfectCentralCoverTorusNormalizer

/-!
# Five-primary transfer from an equivariant diagonal-torus lift

Let P be the actual determinant-one diagonal torus extended by its coordinate
five-cycle. A permutation-equivariant lift of the torus has image L normalized
by every lift of the five-cycle. The full torus preimage A is abelian, so the
derived subgroup of the full P-preimage lies in [A, B], where B is generated
by a lift of the cycle. Replacing torus elements by their section representatives
shows [A, B] ≤ L. Central transfer places a central kernel of order five in
that derived subgroup, contradicting injectivity of the projection on L.

This argument needs no norm-surjectivity assertion and no order assertion for
the lifted five-cycle. The deliberate `import all` reuses the existing private
abelian-by-cyclic derived-subgroup calculation without changing its boundary.

The actual monomial subgroup order 5⁵ and the existence of the equivariant
torus lift remain explicit, independent mathematical obligations. The final
export is a conditional application to the literal `PrimeLocalSections`
contract, not the completed multiplier theorem. The independent ambient order
bound is also explicit, as in the parent odd-prime calculation.

Source: Aschbacher--Smith I.1.1--2 and I.1.4(4), `refs/quasithin.pdf`,
printed pp.407--408; GLS III Section 6.1, `refs/KGroup/GLS3/chapter6.tex`.
-/

public section
open Subgroup PerfectCentralCovering
open scoped commutatorElement

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five

private theorem false_of_normalized_torus_lift
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (d : Cover E G) (hd : Nat.card d.toMonoidHom.ker = 5)
    (T : Subgroup G) (c : G) (hc : c ∈ normalizer (T : Set G))
    (hi : ¬ 5 ∣ (T ⊔ zpowers c).index)
    (hA : IsMulCommutative (T.comap d.toMonoidHom))
    (s : T →* E) (hs : d.toMonoidHom.comp s = T.subtype)
    (hn : ∀ b : E, d.toMonoidHom b = c → b ∈ normalizer (s.range : Set E)) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsPerfect E := d.isPerfect
  let f := d.toMonoidHom
  change Nat.card f.ker = 5 at hd
  obtain ⟨b, hb⟩ := d.surjective c
  change f b = c at hb
  let A := T.comap f
  let B := zpowers b
  let L := s.range
  have hBA : B ≤ normalizer (A : Set E) := by
    apply zpowers_le.mpr
    apply mem_normalizer_iff.mpr
    intro a
    change f a ∈ T ↔ f (b*a*b⁻¹) ∈ T
    simpa only [map_mul, map_inv, hb] using mem_normalizer_iff.mp hc (f a)
  have hBL : B ≤ normalizer (L : Set E) := zpowers_le.mpr (hn b hb)
  have hgen : A ⊔ B = (T ⊔ zpowers c).comap f := by
    have he : (A ⊔ B).map f = T ⊔ zpowers c := by
      rw [Subgroup.map_sup, map_comap_eq_self_of_surjective d.surjective,
        MonoidHom.map_zpowers, hb]
    rw [← he, comap_map_eq_self]
    exact (T.ker_le_comap f).trans le_sup_left
  have hAB : ⁅A, B⁆ ≤ L := by
    apply commutator_le.mpr
    intro a ha y hy
    let t : T := ⟨f a, ha⟩
    have hst : f (s t) = f a := DFunLike.congr_fun hs t
    rw [CentralExtension.commutator_eq_of_image_eq f d.ker_le_center hst.symm rfl]
    exact le_normalizer_iff_commutator_le_left.mp hBL
      (commutator_mem_commutator (show s t ∈ L from ⟨t, rfl⟩) hy)
  have hkp : IsPGroup 5 f.ker := IsPGroup.of_card (n := 1) (by simpa using hd)
  have hkder : f.ker ≤ ⁅A ⊔ B, A ⊔ B⁆ := by
    apply central_pSubgroup_le_commutator (A ⊔ B) f.ker
      (by rw [hgen]; exact (T ⊔ zpowers c).ker_le_comap f) d.ker_le_center hkp
    rw [hgen, index_comap_of_surjective _ d.surjective]
    exact hi
  have hkL : f.ker ≤ L := hkder.trans
    ((PerfectCentralCovering.derived_join_le A B hA inferInstance hBA).trans hAB)
  have hkbot : f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨t, rfl⟩ := hkL hz
    have ht : (t : G) = 1 := by
      exact (DFunLike.congr_fun hs t).symm.trans (MonoidHom.mem_ker.mp hz)
    have ht1 : t = 1 := Subtype.ext ht
    simp [ht1]
  have hcard : Nat.card f.ker = 1 := by rw [hkbot]; exact Subgroup.card_bot
  omega

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open BenderSuzuki.MatrixGroups

omit [Finite F] in
/-- The independent ambient order bound makes the monomial subgroup
prime to five in index once its order is known. -/
theorem monomial_index_prime_to_five_of_card
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    (hP : Nat.card (monomial J hJ hconj) = 5^5)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41) :
    ¬ 5 ∣ (monomial J hJ hconj).index := by
  intro hi
  have h6 : 5^6 ∣ Nat.card J.specialSubgroup := by
    rw [← (monomial J hJ hconj).card_mul_index, hP]
    exact Nat.mul_dvd_mul_left (5^5) hi
  have h := h6.trans hG
  norm_num at h

/-- An equivariant lift of the actual diagonal torus excludes a central
covering kernel of order five when the monomial subgroup has the expected order. -/
theorem no_five_cover_of_monomial_card_and_permutation_lift
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    (hP : Nat.card (monomial J hJ hconj) = 5^5)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41)
    {E : Type*} [Group E] [Finite E] (d : Cover E J.specialSubgroup)
    (hd : Nat.card d.toMonoidHom.ker = 5)
    (hlift : HasPermutationTorusLift J hJ hconj d) : False := by
  obtain ⟨s, hs, hperm⟩ := hlift
  let e : DiagonalCoordinates F ≃* torus J hJ hconj :=
    MonoidHom.ofInjective (diagonal_injective J hJ hconj)
  let sT := s.comp e.symm.toMonoidHom
  have hsT : d.toMonoidHom.comp sT = (torus J hJ hconj).subtype := by
    apply MonoidHom.ext
    intro t
    have h := DFunLike.congr_fun hs (e.symm t)
    exact h.trans (congrArg Subtype.val (e.apply_symm_apply t))
  have hrange : sT.range = s.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map]
  apply false_of_normalized_torus_lift d hd (torus J hJ hconj) (cycle J hJ)
    (permutation_mem_normalizer J hJ hconj (finRotate 5))
    (monomial_index_prime_to_five_of_card J hJ hconj hP hG)
    (torus_preimage_commutative J hJ hconj d.toMonoidHom d.surjective d.ker_le_center)
    sT hsT
  intro b hb
  rw [hrange]
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨permute _ (finRotate 5) a, (hperm (finRotate 5) b hb a).symm⟩
  · rintro ⟨a, ha⟩
    have hb' : d.toMonoidHom b⁻¹ = permutation J hJ (finRotate 5)⁻¹ := by
      rw [map_inv, hb, map_inv]
    refine ⟨permute _ (finRotate 5)⁻¹ a, ?_⟩
    rw [← hperm (finRotate 5)⁻¹ b⁻¹ hb' a, ha]
    group

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
open BenderSuzuki.MatrixGroups Five
universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

/-- Conditional assembly for the literal local-section contract. Its two
monomial premises are retained for their independent construction. -/
theorem five_primeLocalSections_of_monomial_card_and_permutation_lifts
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    (hP : Nat.card (monomial J hJ hconj) = 5^5)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41)
    (hlift : ∀ (E : Type u) [Group E] [Finite E] (d : Cover E J.specialSubgroup),
      Nat.card d.toMonoidHom.ker = 5 → HasPermutationTorusLift J hJ hconj d) :
    PrimeLocalSections J 5 := by
  intro E _ _ d hd
  exact (no_five_cover_of_monomial_card_and_permutation_lift
    J hJ hconj hP hG d hd (hlift E d hd)).elim

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
