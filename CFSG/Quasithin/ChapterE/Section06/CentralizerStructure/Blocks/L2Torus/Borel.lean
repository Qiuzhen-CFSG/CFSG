module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The Borel quotient of an even rank-one block

The upper-left matrix entry maps the triangular Borel onto the multiplicative
field group, with kernel the upper root group. Counting this kernel gives the
Borel order and its index. A Sylow two-subgroup inside the full Borel preimage
is exactly the root-group preimage, so the Borel normalizes it.

These are the quotient calculations in Aschbacher–Smith E.6.7, printed p.246.
The SL₂ order formula is the separately attributed ATLAS port `card_sl_two`.
No block-center or covering-module conclusion is assumed here.
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {F : Type*} [Field F]

private theorem borel_diagonal_ne_zero (g : rankOneBorel F) : g.val.val 0 0 ≠ 0 := by
  have hd : g.val.val 0 0 * g.val.val 1 1 = 1 := by
    simpa only [det_fin_two, (mem_rankOneBorel_iff g.val).mp g.property,
      mul_zero, sub_zero] using g.val.property
  exact left_ne_zero_of_mul_eq_one hd

noncomputable def diagonalProjection : rankOneBorel F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (by exact borel_diagonal_ne_zero g)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [mul_apply, Fin.sum_univ_two, (mem_rankOneBorel_iff h.val).mp h.property]

theorem diagonalProjection_surjective : Function.Surjective (diagonalProjection (F := F)) := by
  intro a
  refine ⟨⟨diag2 a a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩, ?_⟩
  ext
  simp [diagonalProjection, diag2_coe']

theorem diagonalProjection_ker : (diagonalProjection (F := F)).ker =
    (upperUnipotent F).subgroupOf (rankOneBorel F) := by
  ext g
  change diagonalProjection g = 1 ↔ g.val ∈ upperUnipotent F
  constructor
  · intro h
    have h00 : g.val.val 0 0 = 1 := congrArg Units.val h
    have h10 := (mem_rankOneBorel_iff g.val).mp g.property
    have h11 : g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using g.val.property
    refine (mem_upperUnipotent F _).mpr ⟨g.val.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]
  · intro h
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F g.val).mp h
    apply Units.ext
    change g.val.val 0 0 = 1
    rw [← ht]
    simp [transvection_coe]

theorem card_borel [Finite F] : Nat.card (rankOneBorel F) = Nat.card F * (Nat.card F - 1) := by
  have hk : Nat.card (diagonalProjection (F := F)).ker = Nat.card F := by
    rw [diagonalProjection_ker,
      Nat.card_congr (subgroupOfEquivOfLe (upperUnipotent F).le_normalizer).toEquiv,
      card_upperUnipotent]
  have hi : (diagonalProjection (F := F)).ker.index = Nat.card F - 1 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr diagonalProjection_surjective,
      Nat.card_congr (topEquiv : (⊤ : Subgroup Fˣ) ≃* Fˣ).toEquiv, Nat.card_units]
  rw [← (diagonalProjection (F := F)).ker.card_mul_index, hk, hi]

theorem index_borel [Finite F] : (rankOneBorel F).index = Nat.card F + 1 := by
  have hq := Finite.one_lt_card (α := F)
  have hc := (rankOneBorel F).index_mul_card
  rw [card_borel, Atlas.card_sl_two] at hc
  have hmul : (Nat.card F + 1) * (Nat.card F * (Nat.card F - 1)) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    have hsub : (Nat.card F + 1) * (Nat.card F - 1) = Nat.card F ^ 2 - 1 := by
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card F),
        Nat.sub_add_cancel (by nlinarith : 1 ≤ Nat.card F ^ 2)]
    calc
      _ = Nat.card F * ((Nat.card F + 1) * (Nat.card F - 1)) := by ring
      _ = _ := by rw [hsub]
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hq)) (hc.trans hmul.symm)

variable {L : Type*} [Group L] [Finite F] [CharP F 2]

theorem sylow_eq_root_comap (f : L →* SL(2, F)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (S : Sylow 2 L)
    (hS : (S : Subgroup L) ≤ (rankOneBorel F).comap f) :
    (S : Subgroup L) = (upperUnipotent F).comap f := by
  let P : Sylow 2 L := (upperUnipotentSylow F 2).comapOfKerIsPGroup f hker
    (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)
  let B := (rankOneBorel F).comap f
  have hP : (P : Subgroup L) ≤ B := comap_mono (upperUnipotent F).le_normalizer
  have hn : B ≤ normalizer (P : Set L) := le_normalizer_comap f
  let : (P.subtype hP : Subgroup B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hP).mpr hn
  have hle : (P.subtype hP : Subgroup B) ≤ S.subtype hS :=
    (P.subtype hP).isPGroup'.le_sylow_of_normal (S.subtype hS)
  have he : S.subtype hS = P.subtype hP := by
    apply Sylow.ext
    exact (P.subtype hP).is_maximal' (S.subtype hS).isPGroup' hle
  exact congrArg Sylow.toSubgroup (Sylow.subtype_injective he)

theorem borel_comap_normalizes_sylow (f : L →* SL(2, F))
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (S : Sylow 2 L)
    (hS : (S : Subgroup L) ≤ (rankOneBorel F).comap f) :
    (rankOneBorel F).comap f ≤ normalizer (S : Set L) := by
  rw [← S.coe_coe, sylow_eq_root_comap f hf hker S hS]
  exact le_normalizer_comap f

end CFSG.Quasithin.ChapterE.Section06.L2Torus
