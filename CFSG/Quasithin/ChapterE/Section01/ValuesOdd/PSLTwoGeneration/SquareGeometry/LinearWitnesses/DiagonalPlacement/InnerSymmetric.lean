module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Sylow
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers.Pairing
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.InnerSymmetric.Fusion
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

/-!
# Positioned S₄ witnesses for inner actors in prime-square PGL₂

Intersect the specified ambient Sylow subgroup with the actual normal PSL₂
image. Its order is divisible by eight. Simplicity and dihedral fusion supply
a cubic in every inner four-group normalizer, so self-centrality recognizes
these normalizers as S₄. Inside an order-eight overlap, pair the actor with
the other four-group. Both four-groups stay in the original inner Sylow.

The inner normalizer of the paired group already has order 24. The
self-centralizer bound in PGL₂ shows that it is the full ambient normalizer.
The actor is nonnormal there, since S₄ has a unique normal four-group.
The order-eight overlap gives the literal Sylow intersection and local model
required by E.1.2. No maximal-overgroup or escape premise is used.

Source: Aschbacher–Smith A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209–210 and 214; the latter cites Asc82a, Lemma 4.10. The bounds include
fields of orders nine and twenty-five.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
namespace DiagonalPlacement.InnerSymmetric
open PrimeGeometry.Inner.SymmetricNormalizers
variable {F : Type*} [Field F] [Finite F]
local instance : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem positioned_of_inner_normalizers
    (T : Sylow 2 (PGL2 F))
    (L : Subgroup (PGL2 F)) [L.Normal]
    (hodd : IsOddPrimePower (Nat.card F))
    (height : 8 ∣ Nat.card L)
    (hnorm : ∀ S : Sylow 2 L, ∀ B : Subgroup L, B ≤ S → IsKleinFour B →
      Nonempty (normalizer (B : Set L) ≃* Equiv.Perm (Fin 4)))
    (A : Subgroup (PGL2 F)) (hA : IsKleinFour A) (hAT : A ≤ T) (hAL : A ≤ L) :
    ∃ B : Subgroup (PGL2 F), B ≤ T ∧ B ≤ L ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup (PGL2 F)) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set (PGL2 F)) ∧
      Nonempty (normalizer (B : Set (PGL2 F)) ≃* Equiv.Perm (Fin 4)) ∧
      ¬ (A.subgroupOf (normalizer (B : Set (PGL2 F)))).Normal := by
  let := hA
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal L
  have h8 : 8 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
    (S.pow_dvd_card_of_pow_dvd_card (show 2 ^ 3 ∣ Nat.card L from height))
  let A₀ := A.subgroupOf L
  let : IsKleinFour A₀ := klein_subgroupOf A L hAL
  have hA₀S : A₀ ≤ (S : Subgroup L) := by
    rw [hS]
    exact fun _ hx => hAT hx
  obtain ⟨B₀, hB₀S, hB₀, hB₀ne, hc, hD₀N, _⟩ :=
    paired_four_of_normalizers S h8 (hnorm S) A₀ hA₀S
  let B := B₀.map L.subtype
  have hB : IsKleinFour B := isKleinFour_map_of_injective B₀ hB₀ L.subtype L.subtype_injective
  let := hB
  have hAmap : A₀.map L.subtype = A := map_subgroupOf_eq_of_le hAL
  have hBne : B ≠ A := by
    intro he
    exact hB₀ne ((map_injective L.subtype_injective) (he.trans hAmap.symm))
  have hBT : B ≤ T := by
    rintro b ⟨x, hx, rfl⟩
    have hs := hB₀S hx
    rw [hS] at hs
    exact hs
  have hDmap : (A₀ ⊔ B₀).map L.subtype = A ⊔ B := by rw [Subgroup.map_sup, hAmap]
  have hDN : A ⊔ B ≤ normalizer (B : Set (PGL2 F)) := by
    rw [← hDmap]
    exact (map_mono hD₀N).trans (le_normalizer_map L.subtype)
  let H₀ := normalizer (B₀ : Set L)
  obtain ⟨e₀⟩ := hnorm S B₀ hB₀S hB₀
  have hHeq : H₀.map L.subtype = normalizer (B : Set (PGL2 F)) := by
    apply eq_of_le_of_card_ge (le_normalizer_map L.subtype)
    rw [card_map_of_injective L.subtype_injective]
    have hc₀ : Nat.card H₀ = 24 := by
      rw [Nat.card_congr e₀.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num
    rw [hc₀]
    exact normalizer_card_le B (pgl2_kleinFour_centralizer_eq_self F hodd B hB)
  let eH : normalizer (B : Set (PGL2 F)) ≃* Equiv.Perm (Fin 4) :=
    (MulEquiv.subgroupCongr hHeq).symm.trans
      ((equivMapOfInjective H₀ L.subtype L.subtype_injective).symm.trans e₀)
  refine ⟨B, hBT, map_subtype_le B₀, hB, hBne, ?_, hDN, ⟨eH⟩, ?_⟩
  · rw [← hDmap, card_map_of_injective L.subtype_injective]
    exact hc
  · intro hnormal
    have hAN : A ≤ normalizer (B : Set (PGL2 F)) := le_sup_left.trans hDN
    have hBN : B ≤ normalizer (B : Set (PGL2 F)) := le_normalizer
    let : IsKleinFour (A.subgroupOf (normalizer (B : Set (PGL2 F)))) :=
      klein_subgroupOf _ _ hAN
    let : IsKleinFour (B.subgroupOf (normalizer (B : Set (PGL2 F)))) :=
      klein_subgroupOf _ _ hBN
    let := hnormal
    have he := (normal_four_eq_core eH (A.subgroupOf (normalizer (B : Set (PGL2 F))))).trans
      (normal_four_eq_core eH (B.subgroupOf (normalizer (B : Set (PGL2 F))))).symm
    have he' := congrArg (fun K => K.map (normalizer (B : Set (PGL2 F))).subtype) he
    rw [map_subgroupOf_eq_of_le hAN, map_subgroupOf_eq_of_le hBN] at he'
    exact hBne he'.symm

private theorem eight_dvd_inner_card {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) :
    8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  rw [← Nat.card_congr (psl2EquivToPGLRange F).toEquiv,
    psl2_card_formula F (show IsOddPrimePower (Nat.card F) from ⟨p, 2, hp, ho, by decide, hF⟩)]
  have h8 : 8 ∣ Nat.card F - 1 := by
    rw [hF]
    exact Nat.eight_dvd_sq_sub_one_of_odd ho
  have h2 : 2 ∣ Nat.card F + 1 := by
    have hq : Odd (Nat.card F) := hF ▸ ho.pow
    obtain ⟨k, hk⟩ := hq
    exact ⟨k + 1, by omega⟩
  apply Nat.dvd_div_of_mul_dvd
  have h16 : 16 ∣ Nat.card F ^ 2 - 1 := by
    have he : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    rw [he]
    exact Nat.mul_dvd_mul h2 h8
  exact dvd_mul_of_dvd_right h16 _

private theorem inner_normalizer_symmetric
    (hodd : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    (L : Subgroup (PGL2 F)) (e : L ≃* PSL2 F)
    (S : Sylow 2 L) (h8 : 8 ≤ Nat.card S)
    (B : Subgroup L) (hBS : B ≤ S) (hB : IsKleinFour B) :
    Nonempty (normalizer (B : Set L) ≃* Equiv.Perm (Fin 4)) := by
  let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup L := e.isSimpleGroup
  have hL : 4 < Nat.card L := lt_of_lt_of_le (by omega : 4 < Nat.card S)
    (Nat.le_of_dvd Nat.card_pos S.card_subgroup_dvd_card)
  have hcubic := Fusion.exists_order_three_of_simple_dihedral
    (hasDihedralSylowTwo_of_mulEquiv e (psl2_odd_hasDihedralSylowTwo_model F hodd))
    hL S B hB hBS
  let := hB
  exact normalizer_equiv_of_cubic S h8 B hBS
    (PrimeGeometry.kleinFour_selfCentralizing_of_embedding hodd L.subtype
      L.subtype_injective B hB) hcubic

/-- The actor pairs with a distinct inner four-group in the specified Sylow.
Its full PGL₂ normalizer is S₄, with an order-eight overlap and nonnormal actor. -/
theorem exists_paired_inner_normalizer
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (T : Sylow 2 (PGL2 F))
    (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ (T : Subgroup (PGL2 F)))
    (hAL : A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    ∃ B : Subgroup (PGL2 F), B ≤ (T : Subgroup (PGL2 F)) ∧
      B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup (PGL2 F)) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set (PGL2 F)) ∧
      Nonempty (normalizer (B : Set (PGL2 F)) ≃* Equiv.Perm (Fin 4)) ∧
      ¬ (A.subgroupOf (normalizer (B : Set (PGL2 F)))).Normal := by
  let L : Subgroup (PGL2 F) := Matrix.ProjectiveSpecialLinearGroup.toPGL.range
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hF⟩
  let : L.Normal := normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hodd)
  have height : 8 ∣ Nat.card L := eight_dvd_inner_card hp ho hF
  apply positioned_of_inner_normalizers T L hodd height _ A hA hAT hAL
  intro S B hBS hB
  have h8 : 8 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
    (S.pow_dvd_card_of_pow_dvd_card (show 2 ^ 3 ∣ Nat.card L from height))
  exact inner_normalizer_symmetric hodd (by omega) L (psl2EquivToPGLRange F).symm
    S h8 B hBS hB

/-- The exact unconditional inner-witness input to the prime-square
PGL₂ diagonal-placement assembly. -/
theorem exists_inner_symmetric
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (T : Sylow 2 (PGL2 F))
    (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ (T : Subgroup (PGL2 F)))
    (hAL : A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    ∃ H D : Subgroup (PGL2 F), A ≤ H ∧ D ≤ (T : Subgroup (PGL2 F)) ∧
      D ≤ H ∧ Nat.card D = 8 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
        ¬ (A.subgroupOf H).Normal := by
  obtain ⟨B, hBT, _, _, _, hD, hDN, he, hn⟩ :=
    exists_paired_inner_normalizer hp ho hlarge hF T A hA hAT hAL
  exact ⟨normalizer (B : Set (PGL2 F)), A ⊔ B, le_sup_left.trans hDN,
    sup_le hAT hBT, hDN, hD, he, hn⟩

/-- The constructed S₄ has the literal ambient Sylow intersection and
is the nonnormal-actor alternative of `PrimeGeometry.LocalModel`. -/
theorem exists_inner_localModel
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (T : Sylow 2 (PGL2 F))
    (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ (T : Subgroup (PGL2 F)))
    (hAL : A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    ∃ H D : Subgroup (PGL2 F), A ≤ H ∧ D ≤ (T : Subgroup (PGL2 F)) ∧
      D ≤ H ∧ Nat.card D = 8 ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H := by
  obtain ⟨H, D, hAH, hDT, hDH, hD, ⟨eH⟩, hn⟩ :=
    exists_inner_symmetric hp ho hlarge hF T A hA hAT hAL
  exact ⟨H, D, hAH, hDT, hDH, hD,
    PrimeGeometry.Inner.sylow_intersection_symmetric_four T D H hDT hDH hD eH,
    Or.inl ⟨⟨eH⟩, hn⟩⟩

end DiagonalPlacement.InnerSymmetric
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
