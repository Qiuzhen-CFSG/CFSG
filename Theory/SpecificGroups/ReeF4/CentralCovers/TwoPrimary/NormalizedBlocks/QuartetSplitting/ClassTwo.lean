module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.FieldInvariants
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.DefectVanishing.ScalarStem
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.LocalCover
-- This is an internal extension of the existing scalar-norm argument: its
-- final norm step only needs class two, not vanishing of all triple maps.
import all Theory.SpecificGroups.Suzuki.SchurFamilySplitting.DefectVanishing.ScalarStem

/-!
# Splitting a Suzuki covering from class two of its lifted root group

A three-dimensional binary cube suffices to kill scalar-invariant pairings.
Thus the pairing calculation also holds over the field of eight elements.
Once the lifted Suzuki root group has class at most two, the existing torus
norm argument kills its stem kernel, and hence the full covering kernel.

The class-two premise is deliberately retained: it is false in general for
covers of Sz(8), whose multiplier is E₄. For an embedded Sz(8) in a Ree double
cover, it must be proved using ambient relations. No triple-map vanishing
over GF(8) is asserted.

Source: Aschbacher–Smith I.1.1–3, printed p.407, and GLS3 §6.1.
-/

public section
universe u v
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
open Finset Multiplicative

private theorem cube_product {C : Type*} [CommGroup C]
    (f : (Fin 3 → ZMod 2) → C) (l : Fin 3)
    (hf : ∀ v, f (Function.update v l (v l + 1)) = f v)
    (hsq : ∀ v, f v * f v = 1) : ∏ v, f v = 1 := by
  classical
  apply Finset.prod_ninvolution (fun v => Function.update v l (v l + 1))
  · intro v
    rw [hf, hsq]
  · intro v _ he
    have hh := congrFun he l
    simp at hh
  · intro v
    exact mem_univ _
  · intro v
    ext i
    by_cases hi : i = l
    · subst i
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · simp [Function.update_of_ne hi]

private theorem unused_coordinate (i j : Fin 3) : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
  classical
  have hcard : ({i, j} : Finset (Fin 3)).card < (univ : Finset (Fin 3)).card := by
    have h := card_insert_le i ({j} : Finset (Fin 3))
    simp only [card_singleton, card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨l, _, hl⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨l, by simpa only [mem_insert, mem_singleton, not_or] using hl⟩

private theorem pairing_square {K C : Type*} [Field K] [CharP K 2] [CommGroup C]
    (f : Multiplicative K →* C) (x : K) : f (ofAdd x) * f (ofAdd x) = 1 := by
  rw [← map_mul]
  change f (ofAdd (x + x)) = 1
  simp [CharTwo.add_self_eq_zero]

/-- Invariant pairings already vanish in binary dimension three. This includes
GF(8), unlike the independent triple-map vanishing theorem. -/
theorem pairingsVanish_of_three_le_finrank (K : Type u) [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] (hdim : 3 ≤ Module.finrank (ZMod 2) K) :
    ScalarInvariantMaps.PairingsVanish.{u,v} K := by
  classical
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_finrank hdim
  intro C _ b hb
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  change b x y = 1
  have hc : (∏ w : Fin 3 → ZMod 2,
      b (ofAdd ((∑ i, w i • a i) * x.toAdd))
        (ofAdd ((∑ i, w i • a i) * y.toAdd))) = 1 := by
    simp_rw [Finset.sum_mul, ofAdd_sum, map_prod, MonoidHom.finsetProd_apply]
    rw [Finset.prod_comm]
    apply Finset.prod_eq_one
    intro i _
    rw [Finset.prod_comm]
    apply Finset.prod_eq_one
    intro j _
    obtain ⟨l, hli, hlj⟩ := unused_coordinate i j
    apply cube_product _ l
    · intro w
      simp [Ne.symm hli, Ne.symm hlj]
    · intro w
      exact pairing_square _ _
  have hz (w : Fin 3 → ZMod 2) : (∑ i, w i • a i) = 0 ↔ w = 0 :=
    (Fintype.linearCombination (ZMod 2) a).map_eq_zero_iff
      ha.fintypeLinearCombination_injective
  have he : (∏ w : Fin 3 → ZMod 2,
      b (ofAdd ((∑ i, w i • a i) * x.toAdd))
        (ofAdd ((∑ i, w i • a i) * y.toAdd))) = (b x y) ^ 7 := by
    calc
      _ = ∏ w : Fin 3 → ZMod 2, if w = 0 then 1 else b x y := by
        apply Finset.prod_congr rfl
        intro w _
        split_ifs with hw
        · simp [hw]
        · exact hb (Units.mk0 _ (mt (hz w).mp hw)) x y
      _ = _ := by
        simp [Finset.prod_ite, Finset.filter_ne', Fintype.card_pi, ZMod.card]
  have hs : b x y * b x y = 1 := by
    simpa only [ofAdd_toAdd] using pairing_square (b x) y.toAdd
  have hp : (b x y) ^ 7 = b x y := by
    change (b x y) ^ (2 * 3 + 1) = b x y
    rw [pow_add, pow_mul, pow_two, hs]
    simp
  rw [he, hp] at hc
  exact hc

/-- The final scalar norm step, with class two supplied directly. -/
theorem stem_kernel_eq_bot_of_class_two {K P : Type} [Field K] [Group P]
    [Finite K] [CharP K 2] (d : ScalarInvariantMaps.StemData K P)
    (h₂ : ScalarInvariantMaps.PairingsVanish.{0,0} K)
    (hc : _root_.commutator P ≤ Subgroup.center P) : d.kernel = ⊥ := by
  classical
  let _ := Fintype.ofFinite K
  apply bot_unique
  intro x hx
  have hn := ScalarInvariantMaps.StemData.norm_eq_one_on_commutator d h₂ hc x
    (d.kernel_le_commutator hx)
  rw [ScalarInvariantMaps.StemData.centerNorm_kernel d x hx] at hn
  have hp : (⟨x, hx⟩ : d.kernel) ^ Fintype.card Kˣ = 1 :=
    Subtype.ext (congrArg (fun z : Subgroup.center P => (z : P)) hn)
  have he : (⟨x, hx⟩ : d.kernel) = 1 := by
    apply (d.kernel_isTwoGroup.powEquiv
      (ScalarInvariantMaps.StemData.two_coprime_card_units (F := K))).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hp
  exact congrArg Subtype.val he

open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SchurCover.Family

/-- The marked pairing input for every nonbinary Suzuki field, including q=8. -/
theorem suzuki_pairingsVanish (m : ℕ) (hm : 1 ≤ m) :
    ScalarInvariantMaps.PairingsVanish.{0,v} (Field m) := by
  apply pairingsVanish_of_three_le_finrank
  rw [GaloisField.finrank 2 (by omega)]
  omega

/-- Actual covering-kernel application of the norm criterion. The only local
premise is class two of the literal root preimage under the prescribed map. -/
theorem suzuki_kernel_eq_bot_of_class_two {E : Type} [Group E] [Finite E]
    (m : ℕ) (hm : 1 ≤ m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (hc : _root_.commutator (rootPreimage f) ≤ Subgroup.center (rootPreimage f)) :
    f.toMonoidHom.ker = ⊥ := by
  apply kernel_eq_bot_of_rootProjection_ker f
  exact stem_kernel_eq_bot_of_class_two (rootData (by omega) f)
    (suzuki_pairingsVanish m hm) hc

end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
