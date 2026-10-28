module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.LinearExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.G2Parabolics
public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Excluding the G₂ rows at the original fixed centralizer

For a field of size at least four, the literal marked stabilizer is the
full normalizer of the radical intersection. The intrinsic G₂ radical
classification makes it a root parabolic or a solvable Sylow normalizer.
The actual perfect A₅ residual excludes both. Over the binary field the
derived group has order 6048, so its order lacks the required factor five.
No geometric alternatives or block recognition are assumed.

Source: Aschbacher--Smith C.2.7(3), pp.145--147, and the actual
fixed-centralizer comparison in 14.7.68(2), pp.1071--1072.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_g2_large_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : Type*) [Field k] [Finite k] [CharP k 2]
    (hk4 : 4 ≤ Nat.card k)
    (e : starImage Lu (d.fixedCore u) Lu ≃* Atlas.G2.Model k) : False := by
  have hlarge : 40320 < Nat.card (starImage Lu (d.fixedCore u) Lu) := by
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model]
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hk4 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk4 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^6 * (4^6-1) * (4^2-1)) hh
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  have hi := (ChapterC.C27Source.star_intersection_placement_of_large_order
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) hlarge).1
  let R := (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  let P := (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  have hP : P.map e.toMonoidHom = normalizer (R.map e.toMonoidHom : Set (Atlas.G2.Model k)) := by
    rw [show P = normalizer (R : Set (starImage Lu (d.fixedCore u) Lu)) from
      d.fixedStarM_eq_radicalNormalizer_of_large_order u h hlarge,
      map_equiv_normalizer_eq]
  let t := (subgroupOfEquivOfLe
    (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm.trans (e.subgroupMap P)
  have hres := d.fixedStarM_hasA5TwoResidual_of_source u h
  rcases Atlas.G2.radical_normalizer_parabolic_or_sylow
    (R.map e.toMonoidHom) (hi.map_equiv e) with ⟨a,ha⟩ | ⟨S,hS⟩
  · let b := MulAut.conj a
    let v := t.trans (b.subgroupMap (P.map e.toMonoidHom))
    rw [← hP] at ha
    apply g2_parabolic_impossible hres hk4
    rcases ha with hp | hp
    · exact Or.inl ⟨v.trans (MulEquiv.subgroupCongr hp)⟩
    · exact Or.inr ⟨v.trans (MulEquiv.subgroupCongr hp)⟩
  · rw [← hS] at hP
    let v := t.trans (MulEquiv.subgroupCongr hP)
    let : Group.IsSolvable (normalizer (S : Set (Atlas.G2.Model k))) :=
      Atlas.G2.ParabolicCharacters.sylow_normalizer_isSolvable S
    let : Group.IsSolvable (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :=
      Group.isSolvable_of_isSolvable_injective (f := v.toMonoidHom) v.injective
    exact hres.not_isSolvable

theorem fixedComponent_C27_g2_derived_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : Type*) [Field k] [Finite k] [CharP k 2]
    (e : starImage Lu (d.fixedCore u) Lu ≃* commutator (Atlas.G2.Model k)) : False := by
  obtain ⟨n,hn,hk⟩ := Atlas.G2.LieParabolicSetup.field_card (F := k)
  by_cases hone : n = 1
  · have h5 := (d.fixedStarM_hasA5TwoResidual_of_source u h).five_dvd_card.trans
      (card_dvd_of_le (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    have htwo : Nat.card k = 2 := by simpa [hone] using hk
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary htwo] at h5
    norm_num at h5
  · have hn2 : 1 < n := by omega
    have hk4 : 4 ≤ Nat.card k := by
      rw [hk]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    exact d.fixedComponent_C27_g2_large_row_impossible u h k hk4
      (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel hn2 hk))
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
