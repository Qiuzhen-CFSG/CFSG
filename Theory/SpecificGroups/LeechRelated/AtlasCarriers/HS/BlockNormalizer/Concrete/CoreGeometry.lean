module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreOrder
public import Theory.SpecificGroups.Quaternion.PresentationHom

/-!
# Coordinates and the binary section of the actual HS normalizer core

Three explicit words in the certified Sylow generators commute and square
to the marked elementary generators. Their cyclic power maps give an
injective homomorphism from C₄³ into the actual normalizer two-core: a small
kernel-checked test on two permutation letters detects its kernel. The
already proved core order 64 makes this an isomorphism.

Its involutions are exactly the marked elementary eight. Squaring onto that
eight identifies the quotient by the involutions and intertwines conjugation
with the existing normalizer action. The exact normalizer order and odd index
are also calculated. These are model inputs to HSLocal.NormalizerModule.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423;
GLS3 Table 5.3m. The untrusted word discovery is retained in `CoreGeometry/source/`;
all identities used in the proof are checked by the Lean kernel.
-/

public section

open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.BlockNormalizer.CoreGeometry
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 20000

/-- Words in the original three Sylow generators, in Lean multiplication order. -/
@[expose] def rootWord : Fin 3 → List (Fin 3) :=
  ![[1, 2, 1, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 0], [2, 0]]
/-- Commuting fourth roots of the three marked elementary generators. -/
@[expose] def root (i : Fin 3) : Carrier := evalWord sylowGenerator (rootWord i)

theorem root_square (i : Fin 3) : root i ^ 2 = elementaryGenerator i := by
  have h : ∀ (i : Fin 3) (x : Fin 100),
      ((root i ^ 2 : Carrier) : Equiv.Perm (Fin 100)) x =
        (elementaryGenerator i : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

theorem root_commute (i j : Fin 3) : root i * root j = root j * root i := by
  have h : ∀ (i j : Fin 3) (x : Fin 100),
      ((root i * root j : Carrier) : Equiv.Perm (Fin 100)) x =
        ((root j * root i : Carrier) : Equiv.Perm (Fin 100)) x := by
    apply allFin₃
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j))

private def rootGroup : Subgroup Carrier := closure (Set.range root)
private instance : IsMulCommutative rootGroup :=
  isMulCommutative_closure (by rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩; exact root_commute i j)
open scoped IsMulCommutative

private theorem root_centralizes (i : Fin 3) :
    root i ∈ centralizer (baseElementary : Set Carrier) := by
  rw [baseElementary, elementary, centralizer_closure]
  rintro _ ⟨j, _, rfl⟩
  rw [← root_square]
  exact (Commute.pow_right (show Commute (root i) (root j) from root_commute i j) 2).eq.symm

private theorem rootGroup_le : rootGroup ≤ centralizer (baseElementary : Set Carrier) :=
  (closure_le _).mpr (by rintro _ ⟨i,rfl⟩; exact root_centralizes i)

private def rootInGroup (i : Fin 3) : rootGroup := ⟨root i, subset_closure ⟨i,rfl⟩⟩

private theorem root_fourth (i : Fin 3) : rootInGroup i ^ 4 = 1 := by
  apply Subtype.ext
  change root i ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, root_square]
  let := elementary_isElementaryAbelian 2
  exact elemPow_eq_one_of_isElementaryAbelian (elementaryGenerator i)
    (show elementaryGenerator i ∈ elementary 2 from subset_closure ⟨i, Fin.le_last i, rfl⟩)

private def rootPower (i : Fin 3) : Multiplicative (ZMod 4) →* rootGroup :=
  QuaternionGroup.cyclicPowerHom 4 (rootInGroup i) (root_fourth i)

private theorem rootPower_apply (i : Fin 3) (x : ZMod 4) :
    (rootPower i (Multiplicative.ofAdd x) : Carrier) = root i ^ x.val := by
  have h := QuaternionGroup.cyclicPowerHom_intCast 4 (rootInGroup i) (root_fourth i) (x.val : ℤ)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, zpow_natCast, coe_pow, rootPower, rootInGroup] using
    congrArg Subtype.val h

private def coordinateHom : Multiplicative (Fin 3 → ZMod 4) →* rootGroup where
  toFun x := rootPower 0 (.ofAdd (x.toAdd 0)) * rootPower 1 (.ofAdd (x.toAdd 1)) *
    rootPower 2 (.ofAdd (x.toAdd 2))
  map_one' := by change rootPower 0 1 * rootPower 1 1 * rootPower 2 1 = 1; simp only [map_one, mul_one]
  map_mul' x y := by
    change rootPower 0 (.ofAdd (x.toAdd 0) * .ofAdd (y.toAdd 0)) *
      rootPower 1 (.ofAdd (x.toAdd 1) * .ofAdd (y.toAdd 1)) *
      rootPower 2 (.ofAdd (x.toAdd 2) * .ofAdd (y.toAdd 2)) = _
    simp only [map_mul]
    ac_rfl

private theorem coordinateHom_apply (x : Multiplicative (Fin 3 → ZMod 4)) :
    (coordinateHom x : Carrier) =
      root 0 ^ (x.toAdd 0).val * root 1 ^ (x.toAdd 1).val * root 2 ^ (x.toAdd 2).val := by
  change (rootPower 0 _ : Carrier) * (rootPower 1 _ : Carrier) * (rootPower 2 _ : Carrier) = _
  rw [rootPower_apply, rootPower_apply, rootPower_apply]

private theorem coordinate_kernel_test : ∀ i j k : Fin 4,
    ((root 0 ^ i.val * root 1 ^ j.val * root 2 ^ k.val : Carrier) : Equiv.Perm (Fin 100)) 1 = 1 →
    ((root 0 ^ i.val * root 1 ^ j.val * root 2 ^ k.val : Carrier) : Equiv.Perm (Fin 100)) 4 = 4 →
    i = 0 ∧ j = 0 ∧ k = 0 := by
  apply allFin₃
  decide +kernel

private theorem coordinateHom_injective : Function.Injective coordinateHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  change coordinateHom x = 1 at hx
  have hx' : (coordinateHom x : Carrier) = 1 := congrArg Subtype.val hx
  rw [coordinateHom_apply] at hx'
  have hz := coordinate_kernel_test (x.toAdd 0) (x.toAdd 1) (x.toAdd 2)
    (congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 1) hx')
    (congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 4) hx')
  change x = 1
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2

private def toCore : rootGroup →* pCore 2 baseNormalizer :=
  { toFun := fun x => ⟨⟨x, centralizer_le_normalizer _ (rootGroup_le x.property)⟩, by
      rw [model_core_eq_action_ker, normalizerMonoidHom_ker]
      exact rootGroup_le x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private theorem toCore_injective : Function.Injective toCore := by
  intro x y h
  exact Subtype.ext (congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) h)

def coreCoordinates : Multiplicative (Fin 3 → ZMod 4) →* pCore 2 baseNormalizer :=
  toCore.comp coordinateHom

theorem coreCoordinates_bijective : Function.Bijective coreCoordinates := by
  have hi : Function.Injective coreCoordinates := toCore_injective.comp coordinateHom_injective
  exact hi.bijective_of_nat_card_le (by
    rw [model_core_card]
    change 64 ≤ Nat.card (Fin 3 → ZMod 4)
    simp)

/-- An actual equivalence on the specified normalizer two-core. -/
noncomputable def coreEquiv : pCore 2 baseNormalizer ≃* Multiplicative (Fin 3 → ZMod 4) :=
  (MulEquiv.ofBijective coreCoordinates coreCoordinates_bijective).symm


theorem coreCoordinates_apply (x : Multiplicative (Fin 3 → ZMod 4)) :
    ((coreCoordinates x).val : Carrier) =
      root 0 ^ (x.toAdd 0).val * root 1 ^ (x.toAdd 1).val * root 2 ^ (x.toAdd 2).val :=
  coordinateHom_apply x

instance core_isMulCommutative : IsMulCommutative (pCore 2 baseNormalizer) :=
  .of_comm (fun a b => coreEquiv.injective (by simp only [map_mul, mul_comm]))

private theorem zmodFour_two_eq_zero (x : ZMod 4) (h : x + x = 0) : x = 0 ∨ x = 2 := by
  exact (by decide +kernel : ∀ y : ZMod 4, y + y = 0 → y = 0 ∨ y = 2) x h

private theorem root_even_power_mem (i : Fin 3) (x : ZMod 4) (h : x = 0 ∨ x = 2) :
    root i ^ x.val ∈ baseElementary := by
  rcases h with rfl | rfl
  · exact baseElementary.one_mem
  · change root i ^ 2 ∈ baseElementary
    rw [root_square]
    exact subset_closure ⟨i, Fin.le_last i, rfl⟩

/-- The elements of the core squaring to one are exactly the marked elementary eight. -/
theorem core_involution_iff (q : pCore 2 baseNormalizer) :
    q ^ 2 = 1 ↔ (q.val : Carrier) ∈ baseElementary := by
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := coreCoordinates_bijective.surjective q
    have hxx : x ^ 2 = 1 := coreCoordinates_bijective.injective (by
      rw [map_pow, hq, map_one])
    have hx (i : Fin 3) : x.toAdd i = 0 ∨ x.toAdd i = 2 := by
      apply zmodFour_two_eq_zero
      simpa only [pow_two, toAdd_mul, Pi.add_apply, toAdd_one,
        Pi.zero_apply] using congrArg (fun y : Multiplicative (Fin 3 → ZMod 4) => y.toAdd i) hxx
    rw [coreCoordinates_apply]
    exact baseElementary.mul_mem
      (baseElementary.mul_mem (root_even_power_mem 0 _ (hx 0))
        (root_even_power_mem 1 _ (hx 1))) (root_even_power_mem 2 _ (hx 2))
  · intro hq
    apply Subtype.ext
    apply Subtype.ext
    let := elementary_isElementaryAbelian 2
    exact elemPow_eq_one_of_isElementaryAbelian (q.val : Carrier) hq

theorem elementary_le_core_image :
    baseElementary ≤ (pCore 2 baseNormalizer).map baseNormalizer.subtype := by
  intro x hx
  let := elementary_isElementaryAbelian 2
  have hc : x ∈ centralizer (baseElementary : Set Carrier) :=
    fun y hy => setLike_mul_comm hy hx
  exact ⟨⟨x, baseElementary.le_normalizer hx⟩, by
    rw [model_core_eq_action_ker, normalizerMonoidHom_ker]
    exact hc, rfl⟩

theorem core_fourth_power (q : pCore 2 baseNormalizer) : q ^ 4 = 1 := by
  apply coreEquiv.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  funext i
  change 4 • (coreEquiv q).toAdd i = 0
  exact ZModModule.char_nsmul_eq_zero 4 _

theorem core_square_mem (q : pCore 2 baseNormalizer) :
    ((q.val : Carrier) ^ 2) ∈ baseElementary := by
  have h : (q ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact core_fourth_power q
  simpa only [coe_pow] using (core_involution_iff (q ^ 2)).mp h

/-- The literal square map onto the marked elementary subgroup. -/
@[expose] def squareHom : pCore 2 baseNormalizer →* baseElementary where
  toFun q := ⟨(q.val : Carrier) ^ 2, core_square_mem q⟩
  map_one' := by apply Subtype.ext; exact one_pow 2
  map_mul' a b := by
    apply Subtype.ext
    have h := congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) (mul_pow a b 2)
    exact h

theorem squareHom_apply (q : pCore 2 baseNormalizer) :
    (squareHom q : Carrier) = (q.val : Carrier) ^ 2 := rfl

theorem squareHom_surjective : Function.Surjective squareHom := by
  have hgen (i : Fin 3) :
      elementaryGenerator i ∈ squareHom.range.map baseElementary.subtype := by
    let r : pCore 2 baseNormalizer := toCore (rootInGroup i)
    refine ⟨squareHom r, ⟨r, rfl⟩, ?_⟩
    exact root_square i
  have he : baseElementary ≤ squareHom.range.map baseElementary.subtype :=
    (closure_le _).mpr (by rintro _ ⟨i, _, rfl⟩; exact hgen i)
  intro x
  obtain ⟨y, ⟨q, rfl⟩, hy⟩ := he x.property
  exact ⟨q, Subtype.ext hy⟩

theorem squareHom_ker :
    squareHom.ker = (baseElementary.subgroupOf baseNormalizer).subgroupOf
      (pCore 2 baseNormalizer) := by
  ext q
  change squareHom q = 1 ↔ (q.val : Carrier) ∈ baseElementary
  rw [← core_involution_iff q]
  constructor
  · intro h
    have h' : (q.val : Carrier) ^ 2 = 1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  · intro h
    exact Subtype.ext (congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) h)

/-- Squaring identifies the induced binary action with the original normalizer action. -/
theorem squareHom_conjugation (m : baseNormalizer) (q : pCore 2 baseNormalizer) :
    squareHom (MulAut.conjNormal m q) = baseElementary.normalizerMonoidHom m (squareHom q) := by
  apply Subtype.ext
  change ((m.val * (q.val : Carrier) * m.val⁻¹) ^ 2) =
    m.val * (q.val : Carrier) ^ 2 * m.val⁻¹
  simp only [pow_two]
  group


/-- The actual core modulo its involutions, identified by squaring. -/
noncomputable def squareQuotientEquiv :
    (pCore 2 baseNormalizer ⧸ squareHom.ker) ≃* baseElementary :=
  QuotientGroup.quotientKerEquivOfSurjective squareHom squareHom_surjective

theorem squareQuotientEquiv_mk (q : pCore 2 baseNormalizer) :
    squareQuotientEquiv (QuotientGroup.mk' squareHom.ker q) = squareHom q := by rfl

theorem normalizer_card : Nat.card baseNormalizer = 10752 := by
  obtain ⟨f⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
  have hi : (pCore 2 baseNormalizer).index = 168 :=
    (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_SL
  rw [← (pCore 2 baseNormalizer).card_mul_index, model_core_card, hi]

theorem normalizer_index : baseNormalizer.index = 4125 := by
  have h := baseNormalizer.card_mul_index
  rw [normalizer_card, NormalizerIndex.card_carrier] at h
  omega

theorem normalizer_odd_index : Odd baseNormalizer.index := by
  rw [normalizer_index]
  decide

end Sporadic.LeechRelated.HS.BlockNormalizer.CoreGeometry
