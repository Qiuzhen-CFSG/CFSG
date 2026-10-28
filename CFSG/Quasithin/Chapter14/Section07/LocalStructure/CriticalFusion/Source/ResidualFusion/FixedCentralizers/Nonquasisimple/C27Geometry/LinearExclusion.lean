module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.StarResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics.Transport
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LargeComponentPlacement
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow

/-!
# The exact fixed-core normalizer and the linear-three row

The original H normalizes Rᵤ = O₂(H ∩ C_G(u)), so the literal star
stabilizer normalizes Rᵤ* ∩ Lᵤ*. For a large component the existing
Thompson placement gives the reverse containment. Thus this stabilizer
is the full normalizer, even if Rᵤ* has an outer action.

For SL₃(k) with |k| ≥ 4 the intrinsic radical theorem now identifies it
with a full point or plane parabolic, or with a solvable Sylow normalizer.
The actual perfect A₅ residual excludes both: the parabolic has the
forbidden odd scalar quotient, and the Sylow normalizer is solvable.
For |k| = 2, the factor five already contradicts |SL₃(2)| = 168.
No C.2.7 alternative, MS-pair, or block reconstruction is assumed.

Source: Aschbacher--Smith C.2.7(3)(g), pp.145--147, and the original
fixed-centralizer comparison in 14.7.68(2), pp.1071--1072.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The marked intersection normalizes the actual radical intersection. -/
theorem fixedStarM_le_radicalNormalizer (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) ≤
      normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu)) := by
  let D := Lu ⊔ d.fixedCore u
  let A := ((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf D
  have hn : A ≤ normalizer ((d.fixedCore u).subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq (show d.fixedCore u ≤ D from le_sup_right)]
    intro a ha
    exact d.H_normalizes_fixedCore u h.member h.fixed ha.1.1
  have hn' : starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) ≤
      normalizer (starImage Lu (d.fixedCore u) (d.fixedCore u) :
        Set (StarQuotient Lu (d.fixedCore u))) :=
    (map_mono (f := QuotientGroup.mk' (starKernel Lu (d.fixedCore u))) hn).trans
      (le_normalizer_map _)
  intro x hx
  apply mem_normalizer_iff.mpr
  intro y
  exact mem_normalizer_iff.mp (hn' hx) y.val


/-- The literal marked stabilizer is the entire radical-intersection normalizer. -/
theorem fixedStarM_eq_radicalNormalizer_of_large_order
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hlarge : 40320 < Nat.card (starImage Lu (d.fixedCore u) Lu)) :
    (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) =
      normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu)) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact le_antisymm (d.fixedStarM_le_radicalNormalizer u h)
    (ChapterC.C27Source.star_intersection_placement_of_large_order
      (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
        d.point_mem_U_commutator_K) hlarge).2

open Matrix.PSL3.LinearThree

/-- Exclude every nonbinary linear-three field on the original star component. -/
theorem fixedComponent_C27_linearThree_large_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : Type*) [Field k] [Finite k] [CharP k 2]
    (n : ℕ) (hn : 1 < n) (hk : Nat.card k = 2^n)
    (e : starImage Lu (d.fixedCore u) Lu ≃* SL(3,k)) : False := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have hlarge : 40320 < Nat.card (starImage Lu (d.fixedCore u) Lu) := by
    rw [Nat.card_congr e.toEquiv, DefiningSylow.card_specialLinear]
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hk4 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk4 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^3 * (4^3-1) * (4^2-1)) hh
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  have hi := (ChapterC.C27Source.star_intersection_placement_of_large_order
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) hlarge).1
  let R := (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  let P := (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  have hP : P.map e.toMonoidHom = normalizer (R.map e.toMonoidHom : Set SL(3,k)) := by
    rw [show P = normalizer (R : Set (starImage Lu (d.fixedCore u) Lu)) from
      d.fixedStarM_eq_radicalNormalizer_of_large_order u h hlarge,
      map_equiv_normalizer_eq]
  let t := (subgroupOfEquivOfLe
    (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm.trans (e.subgroupMap P)
  have hres := d.fixedStarM_hasA5TwoResidual_of_source u h
  rcases RadicalNormalizer.radical_normalizer_parabolic_or_sylow
    (R.map e.toMonoidHom) (hi.map_equiv e) hn hk with ⟨a,ha⟩ | ⟨S,hS⟩
  · let b := Matrix.HigherLinear.SubspaceTransport.slConj a
    let v := t.trans (b.subgroupMap (P.map e.toMonoidHom))
    rw [← hP] at ha
    apply LinearParabolics.linearThree_false_of_coordinates hres k hn.le hk
    rcases ha with hp | hp
    · exact Or.inl ⟨v.trans (MulEquiv.subgroupCongr hp)⟩
    · exact Or.inr ⟨v.trans (MulEquiv.subgroupCongr hp)⟩
  · rw [← hS] at hP
    let v := t.trans (MulEquiv.subgroupCongr hP)
    let : Group.IsSolvable (normalizer (S : Set SL(3,k))) :=
      RadicalNormalizer.sylow_normalizer_solvable (by omega) hk S
    let : Group.IsSolvable (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :=
      Group.isSolvable_of_isSolvable_injective (f := v.toMonoidHom) v.injective
    exact hres.not_isSolvable


/-- Include the binary field, excluded by the factor five of the original residual. -/
theorem fixedComponent_C27_linearThree_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : Type*) [Field k] [Finite k] [CharP k 2]
    (e : starImage Lu (d.fixedCore u) Lu ≃* SL(3,k)) : False := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  have hk : Nat.card k = 2^(n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  have hnpos : 0 < (n : ℕ) := by
    have hcard : 1 < Nat.card k := Finite.one_lt_card
    by_contra hzero
    have hz : (n : ℕ) = 0 := by omega
    rw [hk,hz,pow_zero] at hcard
    omega
  by_cases hone : (n : ℕ) = 1
  · have h5 := (d.fixedStarM_hasA5TwoResidual_of_source u h).five_dvd_card.trans
      (card_dvd_of_le (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    rw [Nat.card_congr e.toEquiv,DefiningSylow.card_specialLinear,hk,hone] at h5
    norm_num at h5
  · exact d.fixedComponent_C27_linearThree_large_row_impossible u h k n (by omega) hk e

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
