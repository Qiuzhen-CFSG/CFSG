module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Local
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeSylowContainment
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.GroupTheory.NormalCoreIndexFactorial

/-!
# The derived binary G₂ parabolic in 15.3.49(l)

An index-three overgroup of a Sylow two-subgroup in the actual commutator
model has order 96.  Its index-three coset action has a nontrivial normal
two-core.  The concrete octonion-hexagon normalizer theorem puts that core
normalizer in one of the two root parabolics.  The resulting containment is an
equality after restricting the actual order-192 parabolic to `G₂(2)'`; the
ambient parabolic is never identified with its derived intersection.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1143--1145, clause 15.3.49(l), together with the binary model calculation
of Lemma 14.2.21, printed p.988.
-/

@[expose] public section

open Subgroup
open Atlas.G2
open Atlas.G2.LieParabolicSetup
open Atlas.G2.BinaryParabolicPair
open Atlas.G2.BinaryCore
open Atlas.G2.EvenLocal.NormalizerCover

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

private abbrev D := Atlas.G2.BinaryParabolicPair.DerivedModel

private theorem derived_card : Nat.card D = 6048 := by
  change Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048
  rw [commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

private theorem derived_index : D.index = 2 := by
  have hc := D.card_mul_index
  rw [derived_card, card_Model, Nat.card_eq_fintype_card, ZMod.card] at hc
  omega

private theorem first_card : Nat.card firstParabolic = 192 := by
  have h64 : 64 ∣ Nat.card firstParabolic := by
    simpa only [card_unipotent_binary] using
      card_dvd_of_le unipotent_le_firstParabolic
  have h3 : 3 ∣ Nat.card firstParabolic := by
    have h := orderOf_dvd_natCard (⟨cubicActor, cubicActor_mem⟩ : firstParabolic)
    have ho : orderOf (⟨cubicActor, cubicActor_mem⟩ : firstParabolic) = 3 := by
      simpa only [← Subgroup.orderOf_coe] using cubicActor_order
    rw [ho] at h
    exact h
  have hle := Atlas.G2.BinaryParabolicPair.ThreeObstruction.first_card_le
  have h192 : 192 ∣ Nat.card firstParabolic :=
    (show Nat.Coprime 64 3 by decide).mul_dvd_of_dvd_of_dvd h64 h3
  have hge := Nat.le_of_dvd (Nat.card_pos (α := firstParabolic)) h192
  omega

private theorem shortRoot_not_mem_derived : shortRoot ∉ D := by
  intro h
  change shortRoot ∈ commutator (Atlas.G2.Model (ZMod 2)) at h
  rw [commutator_eq_longRootClosure, ← Atlas.G2.BinaryException.lineSign_kernel] at h
  have hs := MonoidHom.mem_ker.mp h
  rw [shortRoot, Atlas.G2.Binary.lineSign_rootF_one] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

private theorem second_card : Nat.card secondParabolic = 192 :=
  Atlas.G2.BinaryCore.secondParabolic_card

private theorem restricted_card (P : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hP : Nat.card P = 192) {x : Atlas.G2.Model (ZMod 2)}
    (hx : x ∈ P) (hxD : x ∉ D) :
    Nat.card (P.subgroupOf D) = 96 := by
  have hrel : D.relIndex P = 2 := by
    have hdvd := D.relIndex_dvd_index_of_normal (K := P)
    rw [derived_index] at hdvd
    have hne : D.relIndex P ≠ 1 := by
      intro hone
      have hle : P ≤ D := (relIndex_eq_one.mp hone)
      exact hxD (hle hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact (hne h).elim
    · exact h
  have hmul := (D.subgroupOf P).card_mul_index
  have hi : (D.subgroupOf P).index = D.relIndex P := rfl
  rw [hi, hrel, hP] at hmul
  have hcard : Nat.card (D.subgroupOf P) = 96 := by omega
  let e : (P.subgroupOf D) ≃* (D.subgroupOf P) :=
    { toFun := fun y => ⟨⟨y.val.val, y.property⟩, y.val.property⟩
      invFun := fun y => ⟨⟨y.val.val, y.property⟩, y.val.property⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl
      map_mul' := by intro a b; rfl }
  exact (Nat.card_congr e.toEquiv).trans hcard

private theorem restricted_card_conjugate
    (P : Subgroup (Atlas.G2.Model (ZMod 2))) (hP : Nat.card P = 192)
    (hx : shortRoot ∈ P) (g : Atlas.G2.Model (ZMod 2)) :
    Nat.card ((P.map (MulAut.conj g).toMonoidHom).subgroupOf D) = 96 := by
  apply restricted_card (P.map (MulAut.conj g).toMonoidHom)
    (x := g * shortRoot * g⁻¹) ?_ ?_ ?_
  · rw [card_map_of_injective (MulAut.conj g).injective, hP]
  · exact mem_map.mpr ⟨shortRoot, hx, rfl⟩
  · intro hmem
    apply shortRoot_not_mem_derived
    have hnormal := (inferInstance : D.Normal)
    have h' := hnormal.conj_mem (g * shortRoot * g⁻¹) hmem g⁻¹
    have heq : g⁻¹ * (g * shortRoot * g⁻¹) * (g⁻¹)⁻¹ = shortRoot := by
      group
    rw [heq] at h'
    exact h'

private theorem sylow_card (T : Sylow 2 D) : Nat.card T = 32 := by
  rw [Sylow.card_eq_multiplicity, derived_card]
  rw [Nat.factorization_def _ Nat.prime_two]
  have hfactor : (6048 : ℕ) = 2 ^ 5 * 189 := by norm_num
  rw [hfactor, padicValNat_base_pow_mul (by decide) (by norm_num)]
  have hz : padicValNat 2 189 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [hz]
  norm_num

private theorem overgroup_card (T : Sylow 2 D) (Q : Subgroup D)
    (hTQ : (T : Subgroup D) ≤ Q)
    (hindex : (T : Subgroup D).relIndex Q = 3) : Nat.card Q = 96 := by
  have hc := ((T : Subgroup D).subgroupOf Q).card_mul_index
  have he : Nat.card ((T : Subgroup D).subgroupOf Q) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTQ).toEquiv
  have hi : ((T : Subgroup D).subgroupOf Q).index = 3 := hindex
  rw [he, hi, sylow_card T] at hc
  omega

private theorem overgroup_twoCore_ne_bot (T : Sylow 2 D) (Q : Subgroup D)
    (hTQ : (T : Subgroup D) ≤ Q) (hindex : (T : Subgroup D).relIndex Q = 3)
    (hQcard : Nat.card Q = 96) (_hsolv : Group.IsSolvable Q) :
    pCore 2 Q ≠ ⊥ := by
  let S : Subgroup Q := (T : Subgroup D).subgroupOf Q
  have hScard : Nat.card S = 32 := by
    exact (Nat.card_congr (subgroupOfEquivOfLe hTQ).toEquiv).trans (sylow_card T)
  have hSindex : S.index = 3 := hindex
  have hSp : IsPGroup 2 S := by
    apply IsPGroup.of_card (n := 5)
    calc
      Nat.card S = 32 := hScard
      _ = 2 ^ 5 := by norm_num
  apply Theory.GroupTheory.pCore_ne_bot_of_not_card_dvd_factorial_index S hSp
  rw [hQcard, hSindex]
  decide

/-- An index-three solvable overgroup of a Sylow two-subgroup in the actual
`G₂(2)'` commutator is one of the two root-defined parabolics, restricted to
the commutator subgroup. -/
theorem g2_parabolic_identification
    (T : Sylow 2 Atlas.G2.BinaryParabolicPair.DerivedModel)
    (Q : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel)
    (hTQ : (T : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel) ≤ Q)
    (hindex : (T : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel).relIndex Q = 3)
    (hsolv : Group.IsSolvable Q) :
    ∃ (g : Atlas.G2.Model (ZMod 2)) (i : Fin 2),
      Q = ((if i = 0 then parabolic₁ else parabolic₂).map
        (MulAut.conj g).toMonoidHom).subgroupOf
          Atlas.G2.BinaryParabolicPair.DerivedModel := by
  have hQcard := overgroup_card T Q hTQ hindex
  have hcore := overgroup_twoCore_ne_bot T Q hTQ hindex hQcard hsolv
  let R : Subgroup D := (pCore 2 Q).map Q.subtype
  have hR : R ≠ ⊥ := by
    intro h
    apply hcore
    exact ((pCore 2 Q).map_eq_bot_iff_of_injective Q.subtype_injective).mp h
  have hpR : IsPGroup 2 R := pCore_isPGroup.map Q.subtype
  have hNQ : Q ≤ normalizer (R : Set D) := by
    have h := (pCore 2 Q).le_normalizer_map Q.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have hNA : Q.map D.subtype ≤ normalizer (R.map D.subtype : Set (Atlas.G2.Model (ZMod 2))) :=
    (map_mono hNQ).trans (R.le_normalizer_map D.subtype)
  obtain ⟨g, hg | hg⟩ := normalizer_conjugate_le_parabolic (F := ZMod 2)
    (R.map D.subtype) (by
      intro h
      apply hR
      exact ((R.map_eq_bot_iff_of_injective D.subtype_injective).mp h))
      (hpR.map D.subtype)
  · refine ⟨g⁻¹, 0, ?_⟩
    let P : Subgroup (Atlas.G2.Model (ZMod 2)) := parabolic₁
    have hle : Q ≤ (P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D := by
      intro x hx
      have hxmap : x.val ∈ Q.map D.subtype := mem_map.mpr ⟨x, hx, rfl⟩
      have hxnorm : x.val ∈ normalizer (R.map D.subtype : Set (Atlas.G2.Model (ZMod 2))) :=
        hNA hxmap
      rw [Subgroup.mem_subgroupOf]
      have heq : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹))
          (g * x.val * g⁻¹) = x.val := by
        change (MulAut.conj g⁻¹) (g * x.val * g⁻¹) = x.val
        rw [MulAut.conj_apply]
        group
      exact mem_map.mpr ⟨g * x.val * g⁻¹,
        hg (mem_map.mpr ⟨x.val, hxnorm, rfl⟩), heq⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle
    have hP : Nat.card P = 192 := by
      simpa [P, parabolic₁_binary] using first_card
    have hxP : shortRoot ∈ P := by
      simpa [P, parabolic₁_binary] using
        (unipotent_le_firstParabolic shortRoot_mem_unipotent)
    have hcard : Nat.card ((P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D) = 96 :=
      restricted_card_conjugate P hP hxP g⁻¹
    have hcardge : Nat.card ((P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D) ≤
        Nat.card Q := by
      rw [hcard]
      exact hQcard.ge
    simpa [P] using heq hcardge
  · refine ⟨g⁻¹, 1, ?_⟩
    let P : Subgroup (Atlas.G2.Model (ZMod 2)) := parabolic₂
    have hle : Q ≤ (P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D := by
      intro x hx
      have hxmap : x.val ∈ Q.map D.subtype := mem_map.mpr ⟨x, hx, rfl⟩
      have hxnorm : x.val ∈ normalizer (R.map D.subtype : Set (Atlas.G2.Model (ZMod 2))) :=
        hNA hxmap
      rw [Subgroup.mem_subgroupOf]
      have heq : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹))
          (g * x.val * g⁻¹) = x.val := by
        change (MulAut.conj g⁻¹) (g * x.val * g⁻¹) = x.val
        rw [MulAut.conj_apply]
        group
      exact mem_map.mpr ⟨g * x.val * g⁻¹,
        hg (mem_map.mpr ⟨x.val, hxnorm, rfl⟩), heq⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle
    have hP : Nat.card P = 192 := by
      simpa [P, BinaryCore.secondParabolic] using second_card
    have hxP : shortRoot ∈ P := by
      simpa [P] using (unipotent_le_parabolic shortRoot_mem_unipotent)
    have hcard : Nat.card ((P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D) = 96 :=
      restricted_card_conjugate P hP hxP g⁻¹
    have hcardge : Nat.card ((P.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf D) ≤
        Nat.card Q := by
      rw [hcard]
      exact hQcard.ge
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simpa [P, h10] using heq hcardge

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
