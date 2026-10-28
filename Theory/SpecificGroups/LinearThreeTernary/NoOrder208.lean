module

public import Theory.SpecificGroups.PSL3Three.CandidateOrders
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum

/-!
# No subgroup of order 208 in GL₃(3)

The actual automorphism group of the ternary three-space has order 11232,
which is not divisible by five. It has no subgroup of order 208: the
intersection of such a subgroup with SL₃(3) would have order 104 or 208.
In either case Sylow counting makes its Sylow thirteen-subgroup normal.
Sylow conjugacy in SL₃(3) then places the intersection in a normalizer of
order 39, contradicting Lagrange's theorem.

The order 39 is the existing count of the full normalizer of the concrete
Singer subgroup in `PSL3Three.CandidateOrders`; no maximal-subgroup
classification is used. The matrix and linear presentations are connected
by the standard basis isomorphism `matrixEquiv`.

Source: Aschbacher–Smith, final paragraph of J.2.7, printed p.437 (PDF p.448).
-/

public section
open Subgroup Matrix.PSL3Three
namespace LinearThreeTernary

/-- Linear automorphisms of the actual ternary three-space. -/
abbrev LinearGroup := (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)
/-- Invertible three-by-three matrices over the same field. -/
abbrev MatrixGroup := Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)

/-- The standard basis identifies the matrix and linear groups. -/
noncomputable def matrixEquiv : MatrixGroup ≃* LinearGroup :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 3) (Fin 3))).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 3 → ZMod 3))

/-- The ordered-basis formula gives the exact order of GL₃(3). -/
theorem card_linearGroup : Nat.card LinearGroup = 11232 := by
  rw [← Nat.card_congr matrixEquiv.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

private theorem normalizer_card (P : Sylow 13 SL) :
    Nat.card (normalizer (P : Set SL)) = 39 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let S : Sylow 13 SL := Sylow.ofCard singerSubgroupSL (by
    rw [card_singerSubgroupSL, card_SL]
    decide +kernel)
  have hs : (normalizer (S : Set SL)).index = 144 := by
    have h := singerNormalizerSL.card_mul_index
    rw [card_singerNormalizerSL, card_SL] at h
    change singerNormalizerSL.index = 144
    omega
  have hi : (normalizer (P : Set SL)).index = 144 :=
    P.card_eq_index_normalizer.symm.trans (S.card_eq_index_normalizer.trans hs)
  have h := (normalizer (P : Set SL)).card_mul_index
  rw [hi, card_SL] at h
  omega

private theorem no_SL_subgroup (H : Subgroup SL)
    (hH : Nat.card H = 104 ∨ Nat.card H = 208) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 H := default
  have hp : Nat.card P = 13 := by
    rw [P.card_eq_multiplicity]
    rcases hH with h | h <;> rw [h] <;> decide +kernel
  have hi : P.index = 8 ∨ P.index = 16 := by
    have h := (P : Subgroup H).card_mul_index
    change Nat.card P * P.index = Nat.card H at h
    rw [hp] at h
    omega
  have hd : Nat.card (Sylow 13 H) ∣ 16 := by
    rcases hi with hi | hi
    · exact (hi ▸ P.card_dvd_index).trans (by decide)
    · exact hi ▸ P.card_dvd_index
  have hm : Nat.card (Sylow 13 H) % 13 = 1 := by
    simpa [Nat.ModEq] using (card_sylow_modEq_one 13 H)
  have hle : Nat.card (Sylow 13 H) ≤ 16 := Nat.le_of_dvd (by decide) hd
  have hone : Nat.card (Sylow 13 H) = 1 := by
    have he : Nat.card (Sylow 13 H) = 1 ∨ Nat.card (Sylow 13 H) = 14 := by omega
    rcases he with he | he
    · exact he
    · norm_num [he] at hd
  let : Subsingleton (Sylow 13 H) := (Nat.card_eq_one_iff_unique.mp hone).1
  let : (P : Subgroup H).Normal := P.normal_of_subsingleton
  let Q : Subgroup SL := (P : Subgroup H).map H.subtype
  have hq : Nat.card Q = 13 := by
    change Nat.card ((P : Subgroup H).map H.subtype) = 13
    rw [card_map_of_injective H.subtype_injective]
    exact hp
  let S : Sylow 13 SL := Sylow.ofCard Q (by rw [hq, card_SL]; decide +kernel)
  have hleN : H ≤ normalizer (S : Set SL) := by
    have h := (P : Subgroup H).le_normalizer_map H.subtype
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at h
    exact h
  have hdN := card_dvd_of_le hleN
  rw [normalizer_card] at hdN
  rcases hH with hH | hH <;> norm_num [hH] at hdN

private def determinantKernelMap (H : Subgroup MatrixGroup) :
    (Matrix.GeneralLinearGroup.det.comp H.subtype).ker →* SL where
  toFun x := ⟨x.val.val.val, congrArg Units.val x.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem determinantKernelMap_injective (H : Subgroup MatrixGroup) :
    Function.Injective (determinantKernelMap H) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

private theorem no_matrix_subgroup (H : Subgroup MatrixGroup) (hH : Nat.card H = 208) :
    False := by
  let d := Matrix.GeneralLinearGroup.det.comp H.subtype
  have hr : Nat.card d.range ∣ 2 := by
    have h := d.range.card_subgroup_dvd_card
    have hu : Nat.card (ZMod 3)ˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rwa [hu] at h
  have hprod : Nat.card d.ker * Nat.card d.range = 208 := by
    have h := d.ker.card_mul_index
    rwa [index_ker, hH] at h
  have hr12 : Nat.card d.range = 1 ∨ Nat.card d.range = 2 := (Nat.dvd_prime (by decide)).mp hr
  have hk : Nat.card d.ker = 104 ∨ Nat.card d.ker = 208 := by
    rcases hr12 with hr12 | hr12 <;> rw [hr12] at hprod <;> omega
  let f := determinantKernelMap H
  apply no_SL_subgroup f.range
  have hf : Nat.card f.range = Nat.card d.ker :=
    Nat.card_congr (MonoidHom.ofInjective (determinantKernelMap_injective H)).toEquiv.symm
  rwa [hf]

/-- The actual GL₃(3) has no subgroup of order 16 · 13. -/
theorem no_subgroup_order_208 (H : Subgroup LinearGroup) : Nat.card H ≠ 208 := by
  intro hH
  apply no_matrix_subgroup (H.map matrixEquiv.symm.toMonoidHom)
  rwa [card_map_of_injective matrixEquiv.symm.injective]

/-- Five does not divide the order of GL₃(3). -/
theorem not_five_dvd_card : ¬ 5 ∣ Nat.card LinearGroup := by
  rw [card_linearGroup]
  decide

/-- Any group acting faithfully on a ternary three-space has order prime to five. -/
theorem not_five_dvd_card_of_injective {H : Type*} [Group H]
    (f : H →* LinearGroup) (hf : Function.Injective f) : ¬ 5 ∣ Nat.card H :=
  fun h => not_five_dvd_card (h.trans (Subgroup.card_dvd_of_injective f hf))

/-- A faithful three-dimensional ternary representation excludes order 208. -/
theorem card_ne_208_of_injective {H : Type*} [Group H]
    (f : H →* LinearGroup) (hf : Function.Injective f) : Nat.card H ≠ 208 := by
  intro h
  apply no_subgroup_order_208 f.range
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans h

end LinearThreeTernary
