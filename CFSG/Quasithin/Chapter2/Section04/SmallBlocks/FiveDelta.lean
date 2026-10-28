module

public import CFSG.Quasithin.Chapter2.Defs
public import CFSG.Quasithin.ClassicalModels
public import GorensteinWalter.A5
public import GorensteinWalter.LinearRingEquiv
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Empty δ in the actual alternating group on five letters

Every nonidentity two-subgroup of A₅ fixes exactly one letter: the two-group
orbit count supplies a fixed point, and an involution has just one fixed
letter. Its normalizer therefore fixes that letter. Point stabilizers are
two-local, as follows from their explicit normal Klein four-subgroups.
Maximality now identifies each maximal two-local with a point stabilizer,
and all two-subgroups inside it have their normalizers inside it as well.

This proves the δ exclusion of PSL₂(5) used in Aschbacher–Smith, Lemma 2.4.26,
printed p.543, through the actual PSL₂(5) ≃ A₅ equivalence.
-/

public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter2.SmallBlocks

local notation "A5" => alternatingGroup (Fin 5)
private abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)
private def r : A5 := ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def s : A5 := ⟨swap 0 2 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def fourHom : V4 →* A5 where
  toFun i := r ^ i.toAdd.1.val * s ^ i.toAdd.2.val
  map_one' := rfl
  map_mul' := by decide +kernel
private theorem fourHom_injective : Function.Injective fourHom := by decide +kernel
private def four : Subgroup A5 := fourHom.range
private theorem four_card : Nat.card four = 4 := by
  rw [four, ← Nat.card_congr (MonoidHom.ofInjective fourHom_injective).toEquiv]
  simp [V4]
private theorem normalizer_test : ∀ g : A5,
    (∀ i : V4, ∃ j : V4, fourHom j = g * fourHom i * g⁻¹) ↔
      (g : Perm (Fin 5)) 4 = 4 := by decide +kernel
private theorem normalizer_four : normalizer (four : Set A5) =
    MulAction.stabilizer A5 (4 : Fin 5) := by
  apply le_antisymm
  · intro g hg
    apply (normalizer_test g).mp
    intro i
    exact (hg _).mp ⟨i, rfl⟩
  · apply le_normalizer_iff.mpr
    rintro g hg x ⟨i, rfl⟩
    exact (normalizer_test g).mpr hg i

private theorem point_stabilizer_twoLocal (i : Fin 5) :
    IsTwoLocal (MulAction.stabilizer A5 i) := by
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq A5 (4 : Fin 5) i
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  apply Theory.Quasithin.isTwoLocal_map
  refine ⟨four, ?_, IsPGroup.of_card (p := 2) (n := 2) four_card, normalizer_four.symm⟩
  intro hb
  have hc := four_card
  rw [hb, card_bot] at hc
  norm_num at hc

private theorem involution_fixed_unique : ∀ x : A5, x ≠ 1 → x ^ 2 = 1 →
    ∀ i j : Fin 5, x • i = i → x • j = j → i = j := by decide +kernel

private theorem twoSubgroup_fixed_unique (D : Subgroup A5) (hD : D ≠ ⊥)
    (hp : IsPGroup 2 D) : ∃! i : Fin 5, ∀ d : D, d • i = i := by
  obtain ⟨i, hi⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  have hdvd : 2 ∣ Nat.card D := hp.card_eq_or_dvd.resolve_left (fun h => hD (card_eq_one.mp h))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hdvd
  have hne : (x : A5) ≠ 1 := by
    intro h
    have he : x = 1 := Subtype.ext h
    simp [he] at hx
  have hsq : (x : A5) ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one x
    rw [hx] at hpow
    exact congrArg Subtype.val hpow
  exact ⟨i, hi, fun j hj => involution_fixed_unique x hne hsq j i (hj x) (hi x)⟩

private theorem twoSubgroup_normalizer_fixes (D : Subgroup A5) (hD : D ≠ ⊥)
    (hp : IsPGroup 2 D) (i : Fin 5) (hi : ∀ d : D, d • i = i) :
    normalizer (D : Set A5) ≤ MulAction.stabilizer A5 i := by
  obtain ⟨j, hj, hu⟩ := twoSubgroup_fixed_unique D hD hp
  have hji : i = j := hu i hi
  intro g hg
  have hfix : ∀ d : D, d • (g • i) = g • i := by
    intro d
    have hm : g⁻¹ * (d : A5) * g ∈ D := by
      change g⁻¹ * (d : A5) * g ∈ (D : Set A5)
      simpa only [inv_inv] using ((normalizer (D : Set A5)).inv_mem hg (d : A5)).mp d.property
    have he := hi ⟨g⁻¹ * (d : A5) * g, hm⟩
    change (g⁻¹ * (d : A5) * g) • i = i at he
    have he' := congrArg (fun a : Fin 5 => g • a) he
    change (d : A5) • (g • i) = g • i
    simpa only [← mul_smul, mul_inv_cancel_left, mul_assoc] using he'
  exact (hu (g • i) hfix).trans hji.symm

/-- In the actual A₅, every maximal two-local is the stabilizer of a letter. -/
theorem alternating_five_maximalTwoLocal (M : Subgroup A5) (hM : IsMaximalTwoLocal M) :
    ∃ i : Fin 5, M = MulAction.stabilizer A5 i := by
  obtain ⟨D, hD, hp, he⟩ := hM.1
  obtain ⟨i, hi, _⟩ := twoSubgroup_fixed_unique D hD hp
  have hle : M ≤ MulAction.stabilizer A5 i :=
    he ▸ twoSubgroup_normalizer_fixes D hD hp i hi
  exact ⟨i, le_antisymm hle (hM.2 (point_stabilizer_twoLocal i) hle)⟩

/-- Every nonidentity two-subgroup inside an actual A₅ maximal two-local
has its whole normalizer in the same local. -/
theorem alternating_five_twoSubgroup_normalizer_le
    (M D : Subgroup A5) (hM : IsMaximalTwoLocal M) (hD : D ≠ ⊥)
    (hp : IsPGroup 2 D) (hDM : D ≤ M) : normalizer (D : Set A5) ≤ M := by
  obtain ⟨i, rfl⟩ := alternating_five_maximalTwoLocal M hM
  exact twoSubgroup_normalizer_fixes D hD hp i fun d => hDM d.property

/-- δ is empty in every copy of A₅, even for an arbitrary choice of its
characteristic-two test family E. -/
theorem delta_empty_of_alternating_five {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) (E : Set (Subgroup G))
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) : delta E M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro D hD
  apply hD.2.2.2
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [map_equiv_normalizer_eq]
  exact alternating_five_twoSubgroup_normalizer_le _ _
    (Theory.Quasithin.isMaximalTwoLocal_map e hM)
    (fun h => hD.1.1 ((map_eq_bot_iff_of_injective D e.injective).mp h))
    (hD.1.2.map _) (map_mono hD.2.2.1)

/-- The source exclusion of PSL₂(5): its actual five-point geometry makes
the literal nonempty δ hypothesis impossible. -/
theorem not_psl2_five_of_delta_nonempty {G : Type*} [Group G]
    (E : Set (Subgroup G)) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hdelta : (delta E M).Nonempty) : ¬ ClassicalGroup.IsPSL G 2 5 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let ef : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let ea : G ≃* A5 := e.trans ((GorensteinWalter.psl2RingEquiv ef).symm.trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm)
  rw [delta_empty_of_alternating_five ea E M hM] at hdelta
  exact Set.not_nonempty_empty hdelta

end CFSG.Quasithin.Chapter2.SmallBlocks
