module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Coordinates
public import Theory.SpecificGroups.Alternating.OddInvolutionExtension
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The marked product from an odd permutation action

An isomorphism L ≅ Aₙ and the compatible odd involution action of r first
embed Sₙ with image L⟨r⟩. Faithfulness of the Sₙ action on Aₙ makes that
image disjoint from C_G(L). The commuting involution z therefore gives an
independent central factor. Multiplication constructs the isomorphism onto
the actual L⟨r,z⟩ and verifies every marking, including the cycle type of r.
No assertion about LT or ambient fusion is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1192.
-/

@[expose] public section

open Subgroup Equiv Equiv.Perm
open QuaternionGroup (cyclicPowerHom cyclicPowerHom_one)
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G]

/-- Construct all the markings from the action of the outer involution. -/
theorem alternatingProductModel_of_odd_action {L : Subgroup G} {z r : G} {n : ℕ}
    (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n))
    (hz2 : orderOf z = 2) (hr2 : r ^ 2 = 1)
    (hLz : L ≤ centralizer ({z} : Set G))
    (hrz : r ∈ centralizer ({z} : Set G))
    (s : Perm (Fin n)) (hs : s ^ 2 = 1) (hodd : sign s = -1)
    (haction : ∀ k : alternatingGroup (Fin n),
      (e.symm (MulAut.conjNormal s k) : G) = r * (e.symm k : G) * r⁻¹)
    (hcycle : s.cycleType = {2} ∨ n = 8 ∧ s.cycleType = {2, 2, 2}) :
    Nonempty (AlternatingProductModel L z r n) := by
  classical
  let f : alternatingGroup (Fin n) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hfr : f.range = L := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply _)⟩
  obtain ⟨F, hF, hFk, hFs⟩ :=
    Theory.SpecificGroups.Alternating.OddInvolutionExtension.exists_embedding
      hn s hs hodd f hf r hr2 haction
  have hFr : F.range = L ⊔ zpowers r := by
    rw [Theory.SpecificGroups.Alternating.OddInvolutionExtension.range_eq
      s hs hodd f F r hFk hFs, hfr]
  have hFC : Disjoint F.range (centralizer (L : Set G)) := by
    apply disjoint_def.mpr
    rintro x ⟨p, rfl⟩ hp
    have hpC : p ∈ centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      apply hF
      rw [map_mul, map_mul, hFk ⟨a, ha⟩]
      exact mem_centralizer_iff.mp hp (f ⟨a, ha⟩) (e.symm ⟨a, ha⟩).property
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot n hn,
      mem_bot] at hpC
    simp [hpC]
  let c : Multiplicative (ZMod 2) →* G := cyclicPowerHom 2 z (hz2 ▸ pow_orderOf_eq_one z)
  have hc1 : c (Multiplicative.ofAdd 1) = z := cyclicPowerHom_one _ _ _
  have hcr : c.range = zpowers z := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      change ZMod 2 at a
      fin_cases a
      · change c 1 ∈ zpowers z
        rw [map_one]
        exact one_mem _
      · change c (Multiplicative.ofAdd 1) ∈ zpowers z
        rw [hc1]
        exact mem_zpowers z
    · exact zpowers_le.mpr ⟨_, hc1⟩
  have hc : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff c).mp
    apply bot_unique
    intro a ha
    change c a = 1 at ha
    change ZMod 2 at a
    fin_cases a
    · rfl
    · change c (Multiplicative.ofAdd 1) = 1 at ha
      rw [hc1] at ha
      simp [ha] at hz2
  have hzc : z ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro l hl
    exact mem_centralizer_singleton_iff.mp (hLz hl)
  have hcc : c.range ≤ centralizer (L : Set G) := by
    rw [hcr]
    exact zpowers_le.mpr hzc
  have hFc (p : Perm (Fin n)) (a : Multiplicative (ZMod 2)) : Commute (F p) (c a) := by
    have hp : F p ∈ centralizer ({z} : Set G) := by
      apply (sup_le hLz (zpowers_le.mpr hrz))
      rw [← hFr]
      exact ⟨p, rfl⟩
    change ZMod 2 at a
    fin_cases a
    · change Commute (F p) (c 1)
      rw [map_one]
      exact Commute.one_right _
    · change Commute (F p) (c (Multiplicative.ofAdd 1))
      rw [hc1]
      exact mem_centralizer_singleton_iff.mp hp
  let P : (Perm (Fin n) × Multiplicative (ZMod 2)) →* G := F.noncommCoprod c hFc
  have hP : Function.Injective P :=
    (MonoidHom.noncommCoprod_injective F c hFc).mpr ⟨hF, hc, hFC.mono_right hcc⟩
  have hPr : P.range = AlternatingOvergroup L z r := by
    rw [MonoidHom.noncommCoprod_range, hFr, hcr]
  let E : (Perm (Fin n) × Multiplicative (ZMod 2)) ≃* AlternatingOvergroup L z r :=
    (MonoidHom.ofInjective hP).trans (MulEquiv.subgroupCongr hPr)
  have hE (p : Perm (Fin n)) (a : Multiplicative (ZMod 2)) :
      (E (p, a) : G) = F p * c a := rfl
  have hEk (k : alternatingGroup (Fin n)) :
      (E ((k : Perm (Fin n)), 1) : G) = (e.symm k : G) := by
    rw [hE, map_one, mul_one, hFk]
    rfl
  have hEz : E (1, Multiplicative.ofAdd 1) =
      ⟨z, mem_sup_right (mem_zpowers z)⟩ := by
    apply Subtype.ext
    rw [hE, map_one, one_mul, hc1]
  have hEr : E (s, 1) =
      ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩ := by
    apply Subtype.ext
    rw [hE, map_one, mul_one, hFs]
  refine ⟨{
    equiv := E.symm
    component_iff := ?_
    central_image := ?_
    outer_second := ?_
    outer_cycleType := ?_ }⟩
  · intro a
    constructor
    · intro ha
      let k := e ⟨a, ha⟩
      have hka : E ((k : Perm (Fin n)), 1) = a := by
        apply Subtype.ext
        rw [hEk]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)
      rw [← hka, E.symm_apply_apply]
      exact ⟨k.property, rfl⟩
    · rintro ⟨hp, hc⟩
      have ha : (a : G) = (E ((E.symm a).1, 1) : G) := by
        rw [← hc]
        exact congrArg Subtype.val (E.apply_symm_apply a).symm
      rw [ha, hEk ⟨_, hp⟩]
      exact (e.symm ⟨_, hp⟩).property
  · exact E.symm_apply_eq.mpr hEz.symm
  · rw [← hEr, E.symm_apply_apply]
  · rw [← hEr, E.symm_apply_apply]
    exact hcycle

end CFSG.Quasithin.Chapter16.Intersections
