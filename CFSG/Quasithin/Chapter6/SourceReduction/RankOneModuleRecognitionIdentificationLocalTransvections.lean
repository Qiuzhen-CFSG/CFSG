module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreGeometry
public import CFSG.Quasithin.ChapterG.Section03.TwoCore

/-!
# Genuine G.3 recognition on the original quotient action

In the contrary order-four core-intersection branch, the layer image is a
four-group fixing the marked line pointwise and moving every vector by
that line. Convert the actual quotient conjugation action into a binary
linear action, retaining an equivalence of its full faithful images. The
independent reduced-closure theorem proves this image has trivial two-core.

The marked line supplies a nonzero vector whose root group contains that
four-group. Conjugation proves the root-rank hypothesis on its entire orbit.
The repaired G.3 theorem then gives the full actions on the canonical
blocks, their internal space and group decomposition, and all local rank
conclusions. No irreducibility, single-block conclusion, numerical dimension
bound, or later recognition theorem is assumed.

The single binary three-space and ambient four-space/A₇ steps of 6.2.11
remain with the local-analysis assembly, as does the graph argument 6.2.8.
Source: Aschbacher--Smith, 6.2.11, pp.685--686, and G.3.1, pp.337--338.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] (T L R : Subgroup G) (z : G)

def linearize [IsElementaryAbelian 2 (space T L R z)] :
    MulAut (space T L R z) ≃* BinaryLinear.GL (Additive (space T L R z)) where
  toFun a := { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def linearAction [IsElementaryAbelian 2 (space T L R z)] :
    Centralizer z →* BinaryLinear.GL (Additive (space T L R z)) :=
  (linearize T L R z).toMonoidHom.comp (action T L R z)

variable {T L R z} [Finite G] {κ : GroupClass} {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

theorem four_image_G3 (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    letI := (reduced_space h hnatural hz ho hP).elementary
    let A := (linearAction (P : Subgroup G) L R z).range
    ∃ x : Additive (space (P : Subgroup G) L R z), x ≠ 0 ∧
      x.toMul ∈ seedLine (P : Subgroup G) L R z ∧ pCore 2 A = ⊥ ∧
      ChapterG.Section03.Hypotheses A (MulAction.orbit A x) ∧
      ChapterG.Section03.FullAction A (MulAction.orbit A x) ∧
      ChapterG.Section03.Decomposition A (MulAction.orbit A x) ∧
      ChapterG.Section03.LocalStructure A (MulAction.orbit A x) := by
  classical
  let := (reduced_space h hnatural hz ho hP).elementary
  let W := space (P : Subgroup G) L R z
  let C := seedLine (P : Subgroup G) L R z
  let f := action (P : Subgroup G) L R z
  let e := linearize (P : Subgroup G) L R z
  let a := linearAction (P : Subgroup G) L R z
  let A := a.range
  have hA : pCore 2 A = ⊥ := by
    let erange : f.range ≃* A := (e.subgroupMap f.range).trans
      (MulEquiv.subgroupCongr (show f.range.map (e : _ →* _) = A from
        (MonoidHom.range_comp e.toMonoidHom f).symm))
    have heq := pCore_map_iso 2 erange
    rw [action_range_core h hnatural hz ho hP, Subgroup.map_bot] at heq
    exact heq.symm
  obtain ⟨hC, hV, hmove⟩ := four_image_common_center h hnatural hz ho hP hplane hcard
  have hCne : C ≠ ⊥ := by
    intro he
    change Nat.card C = 2 at hC
    rw [he, card_bot] at hC
    contradiction
  obtain ⟨c, hc⟩ := ne_bot_iff_exists_ne_one.mp hCne
  have hc1 : (c : W) ≠ 1 := fun he => hc (Subtype.ext he)
  let x : Additive W := Additive.ofMul c.val
  have hx : x ≠ 0 := hc1
  have hcorder : orderOf (c : W) = 2 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) c) hc1
  have hCgen : zpowers (c : W) = C := eq_of_le_of_card_ge
    (zpowers_le.mpr c.property) (by rw [Nat.card_zpowers, hcorder, hC])
  have hline (v : Additive W) : v ∈ centerLine x ↔ v.toMul ∈ C := by
    rw [mem_centerLine_iff, ← hCgen, mem_zpowers_iff_mem_range_orderOf, hcorder]
    constructor
    · rintro (rfl | rfl)
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp [x]⟩
    · rintro hv
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hv
      have hi2 := Finset.mem_range.mp hi
      interval_cases i
      · left
        apply Additive.toMul.injective
        change v.toMul = 1
        simpa only [pow_zero] using he.symm
      · right
        apply Additive.toMul.injective
        change v.toMul = c.val
        simpa only [pow_one] using he.symm
  let B := ((layer L R).subgroupOf (Centralizer z)).map f
  have hroot : B.map e.toMonoidHom ≤ rootGroup A x := by
    rintro _ ⟨b, hb, rfl⟩
    have hbA : e b ∈ A := by
      obtain ⟨v, hv, rfl⟩ := hb
      exact ⟨v, rfl⟩
    refine ⟨hbA, ?_, ?_⟩
    · intro v hv
      exact congrArg Additive.ofMul ((hmove b hb).1 v.toMul ((hline v).mp hv))
    · intro v
      apply (hline _).mpr
      change b v.toMul / v.toMul ∈ C
      simpa only [div_eq_mul_inv] using (hmove b hb).2 v.toMul
  have hrcard : 2 < Nat.card (rootGroup A x) := by
    have hh := card_le_of_le hroot
    rw [card_map_of_injective e.injective] at hh
    change Nat.card B = 4 at hV
    omega
  have hG3 : ChapterG.Section03.Hypotheses A (MulAction.orbit A x) := by
    refine ⟨?_, ⟨x, rfl⟩, ?_⟩
    · rintro y ⟨g, rfl⟩
      exact fun he => hx (g.val.injective (he.trans (g.val.map_zero).symm))
    · intro y hy
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      change 1 < Group.rank (ChapterG.Section03.rootQuotientImage A (g.val x))
      have hr : 2 < Nat.card (rootGroup A (g.val x)) := by
        rw [← rootGroup_conjugate g.property x, card_map_of_injective (MulAut.conj g.val).injective]
        exact hrcard
      let q := QuotientGroup.mk' (pCore 2 A)
      have hi : Function.Injective q := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk', hA]
      have hcq : Nat.card (ChapterG.Section03.rootQuotientImage A (g.val x)) =
          Nat.card (rootGroup A (g.val x)) :=
        (Nat.card_congr (((rootGroup A (g.val x)).subgroupOf A).equivMapOfInjective q hi).toEquiv).symm.trans
          (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le A (g.val x))).toEquiv)
      let := ChapterG.Section03.rootQuotientImage_elementaryAbelian A (g.val x)
      have hbound : Nat.card (ChapterG.Section03.rootQuotientImage A (g.val x)) ≤
          2 ^ Group.rank (ChapterG.Section03.rootQuotientImage A (g.val x)) :=
        Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)))
      by_contra hn
      have hp := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (not_lt.mp hn)
      rw [hcq] at hbound
      omega
  exact ⟨x, hx, c.property, hA, hG3,
    ChapterG.Section03.source_conclusions_of_twoCore_eq_bot hG3 hA⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
