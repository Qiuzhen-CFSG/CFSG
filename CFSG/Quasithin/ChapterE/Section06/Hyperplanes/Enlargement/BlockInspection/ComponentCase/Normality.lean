module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.Reduction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Transport
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Relative normality of a small block inside A₆

Two commuting A₃/A₅ blocks cannot both lie in a subgroup of order 360.
Their elementary commutator layers B and D each have a quotient of order at
least four. Commutation puts B ∩ D inside the fixed layer of B, so their
join is a two-group of order at least sixteen. Its order cannot divide 360.

For x ∈ C_X(U), transport the original block by x and apply exact C.1.9 in
C_G(U). The commuting alternative is impossible by that order calculation;
hence x normalizes L. This proves normality inside C_X(U), without assuming
normality in the ambient group or taking it from a model label.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9 and
C.1.12, printed pp.123–124; the A₆ configuration in E.6.23, p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem small_module_card {L : Type*} [Group L] [Finite L]
    (h : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5) :
    4 ≤ Nat.card (BlockModule L) := by
  rcases h with h | h
  · rw [h.module_card_odd (by decide)]
    norm_num
  · rw [h.module_card_odd (by decide)]
    norm_num

private theorem short_of_small {L : Type*} [Group L]
    (h : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5) : IsShort L :=
  h.elim (fun h => h.2.1) (fun h => h.2.1)

/-- The actual block modules force too large a two-subgroup if the blocks commute. -/
theorem smallBlocks_not_commute_in_order360 {L J X : Subgroup G}
    (hL : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5)
    (hJ : IsAlternatingBlock J 3 ∨ IsAlternatingBlock J 5)
    (hLX : L ≤ X) (hJX : J ≤ X) (hX : Nat.card X = 360)
    (hcomm : ⁅L,J⁆ = ⊥) : False := by
  let B := (blockU L).map L.subtype
  let D := (blockU J).map J.subtype
  let Z := (blockU L ⊓ center L).map L.subtype
  have hBL : B ≤ L := map_subtype_le _
  have hDJ : D ≤ J := map_subtype_le _
  have hLJ := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hBD : B ≤ centralizer (D : Set G) :=
    hBL.trans (hLJ.trans (Subgroup.centralizer_le hDJ))
  have hnorm : D ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.mp hBD).trans (centralizer_le_normalizer _)
  let _ := (short_of_small hL).elementary
  let _ := (short_of_small hJ).elementary
  have hBp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 (blockU L)).map L.subtype
  have hDp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 (blockU J)).map J.subtype
  have hsup : IsPGroup 2 (B ⊔ D : Subgroup G) := hBp.to_sup_of_normal_left' hDp hnorm
  have hIZ : B ⊓ D ≤ Z := by
    rintro _ ⟨⟨l, hl, rfl⟩, hlD⟩
    refine ⟨l, ⟨hl, ?_⟩, rfl⟩
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hLJ k.property) l (hDJ hlD)).symm
  have hZidx : Z.relIndex B = Nat.card (BlockModule L) := by
    dsimp [Z, B]
    rw [relIndex_map_map_of_injective _ _ L.subtype_injective, inf_relIndex_left]
    change (blockFixed L).index = Nat.card (BlockModule L)
    exact (blockFixed L).index_eq_card
  have hidx : 4 ≤ (B ⊓ D).relIndex B := by
    apply (small_module_card hL).trans
    rw [← hZidx]
    exact relIndex_le_of_le_left hIZ Subgroup.index_ne_zero_of_finite
  have hDcard : 4 ≤ Nat.card D := by
    have hm := (small_module_card hJ).trans (Nat.le_of_dvd Nat.card_pos
      (card_quotient_dvd_card (blockFixed J)))
    rwa [← Subgroup.card_map_of_injective J.subtype_injective] at hm
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hnorm
  have htower := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ D) B bot_le inf_le_left
  simp only [relIndex_bot_left] at htower
  have heq : Nat.card D * (B ⊓ D).relIndex B = Nat.card (B ⊔ D : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card (B ⊓ D : Subgroup G))
    calc
      Nat.card (B ⊓ D : Subgroup G) * (Nat.card D * (B ⊓ D).relIndex B) =
          (Nat.card (B ⊓ D : Subgroup G) * (B ⊓ D).relIndex B) * Nat.card D := by ring
      _ = Nat.card B * Nat.card D := by rw [htower]
      _ = _ := hmul
  have hlower : 16 ≤ Nat.card (B ⊔ D : Subgroup G) := by
    rw [← heq]
    exact Nat.mul_le_mul hDcard hidx
  have hdiv : Nat.card (B ⊔ D : Subgroup G) ∣ 360 := by
    rw [← hX]
    exact card_dvd_of_le (sup_le (hBL.trans hLX) (hDJ.trans hJX))
  obtain ⟨n, hn⟩ := hsup.exists_card_eq
  rw [hn] at hdiv hlower
  have hn3 : n ≤ 3 := by
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (by decide : 360 ≠ 0)).mp hdiv
    rwa [show (Nat.factorization 360) 2 = 3 by decide +kernel] at this
  have hu : 2 ^ n ≤ 8 := by
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn3)
  omega


/-- C.1.9 and the two-part of |A₆| give normality in the indicated relative centralizer. -/
theorem smallBlock_normal_in_six_centralizer {M V U L X : Subgroup G}
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hU : U ∈ obstructionFamily M V) (hL : SmallBlock U L) (hLX : L ≤ X)
    (hmodel : Chapter1.Section02.LocalModels.IsAlternating X 6) :
    (L.subgroupOf (X ⊓ centralizer (U : Set G))).Normal := by
  have hcard : Nat.card X = 360 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  apply normal_subgroupOf_of_le_normalizer
  intro x hx
  have hxU : U.map (MulAut.conj x).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (U : Set G) hx.2)
  have hLg := smallBlock_conjugate hL x
  rw [hxU] at hLg
  have hLgX : L.map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨l, hl, rfl⟩
    exact X.mul_mem (X.mul_mem hx.1 (hLX hl)) (X.inv_mem hx.1)
  rcases centralizerBlocks_equal_or_commute h19 h21 hU.1 hU.2.1
      ⟨hL.1, hL.2.1⟩ ⟨hLg.1, hLg.2.1⟩ with he | hc
  · exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  · exact (smallBlocks_not_commute_in_order360 hL.2.2 hLg.2.2 hLX hLgX hcard hc).elim

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
