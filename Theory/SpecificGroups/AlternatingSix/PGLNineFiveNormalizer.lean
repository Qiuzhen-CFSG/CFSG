module

public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.OddSubgroupLeNormalIndexTwo
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Five-subgroup and order-ten normalizers in PGL₂(9)

The five-centralizer in A₆ has order five. The automorphism bound and Sylow's
normalizer congruence give normalizer order ten. The canonical index-two
PSL₂(9) subgroup then gives normalizer order twenty in the actual PGL₂(9).
Every order-ten subgroup has a characteristic Sylow five-subgroup and index
two in its normalizer, so its own normalizer has the same order twenty.

This is the projective normalizer calculation used for the literal C₃ × D₁₀
overlap in the J₃ source, Baumeister, *A characterization of J₃*, Lemma 2.5.
-/

public noncomputable section

open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter

namespace AlternatingSix.PGLNineFiveNormalizer

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The normalizer of an actual five-subgroup in A₆ has order ten. -/
theorem alternating_five_normalizer_card
    (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 5) :
    Nat.card (normalizer (P : Set (alternatingGroup (Fin 6)))) = 10 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (hP ▸ dvd_rfl)
  have ho : orderOf (x : alternatingGroup (Fin 6)) = 5 := (orderOf_coe x).trans hx
  have hg : zpowers (x : alternatingGroup (Fin 6)) = P :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers, ho, hP])
  have hC : Nat.card (centralizer (P : Set (alternatingGroup (Fin 6)))) = 5 := by
    rw [← hg, zpowers_eq_closure, centralizer_closure]
    exact GoldenClassGeometry.centralizer_five x ho
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hA : Nat.card (MulAut P) = 4 := by rw [IsCyclic.card_mulAut, hP]; decide
  have hd := P.card_normalizer_dvd_card_centralizer_mul_card_mulAut
  rw [hC, hA] at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 5 * 4) hd
  have hm := Sylow.card_normalizer_modEq_card (p := 5) (n := 1) (H := P) hP
  rw [alt6_card] at hm
  change _ % 25 = 360 % 25 at hm
  omega

private theorem normalizer_card_in_model {H : Type*} [Group H] [Finite H]
    (e : H ≃* alternatingGroup (Fin 6)) (P : Subgroup H) (hP : Nat.card P = 5) :
    Nat.card (normalizer (P : Set H)) = 10 := by
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, map_equiv_normalizer_eq]
  exact alternating_five_normalizer_card _ ((card_map_of_injective e.injective).trans hP)

/-- The normalizer of an actual five-subgroup in PGL₂(9) has order twenty. -/
theorem five_normalizer_card (P : Subgroup (PGL2 Nine.F)) (hP : Nat.card P = 5) :
    Nat.card (normalizer (P : Set (PGL2 Nine.F))) = 20 := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let L := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range
  have hodd : IsOddPrimePower (Nat.card Nine.F) := by
    rw [Nine.card]
    exact ⟨3, 2, by decide, by decide, by decide, by decide⟩
  have hLi : L.index = 2 := pgl2_psl2Range_index_eq_two Nine.F hodd
  let : L.Normal := normal_of_index_eq_two hLi
  let eL : L ≃* alternatingGroup (Fin 6) :=
    (psl2EquivToPGLRange Nine.F).symm.trans psl2NineCoordinatesEquivAlt6
  have hLc : Nat.card L = 360 := (Nat.card_congr eL.toEquiv).trans alt6_card
  have hGc : Nat.card (PGL2 Nine.F) = 720 := by
    have hh := L.card_mul_index
    rw [hLc, hLi] at hh
    exact hh.symm
  have hPL : P ≤ L := odd_card_subgroup_le_normal_index_two L P inferInstance hLi
    (by rw [hP]; decide)
  let N := normalizer (P : Set (PGL2 Nine.F))
  have hNc : Nat.card (N.subgroupOf L) = 10 := by
    change Nat.card ((normalizer (P : Set (PGL2 Nine.F))).subgroupOf L) = 10
    rw [subgroupOf_normalizer_eq hPL]
    exact normalizer_card_in_model eL _
      ((Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv).trans hP)
  have hNc' : Nat.card (L.subgroupOf N) = 10 := by
    have he : L.subgroupOf N ≃ N.subgroupOf L :=
      ⟨fun x => ⟨⟨x, x.property⟩, x.val.property⟩,
        fun x => ⟨⟨x, x.property⟩, x.val.property⟩,
        fun _ => rfl, fun _ => rfl⟩
    exact (Nat.card_congr he).trans hNc
  have hi : (L.subgroupOf N).index ≤ 2 := by
    have hd := relIndex_dvd_index_of_normal (H := L) (K := N)
    rw [hLi, relIndex] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hh := (L.subgroupOf N).card_mul_index
  rw [hNc'] at hh
  have hb : Nat.card N ≤ 20 := by nlinarith
  have hm := Sylow.card_normalizer_modEq_card (p := 5) (n := 1) (H := P) hP
  rw [hGc] at hm
  change Nat.card N % 25 = 720 % 25 at hm
  change Nat.card N = 20
  omega

/-- Every actual subgroup of order ten in PGL₂(9) has normalizer order twenty. -/
theorem ten_normalizer_card (D : Subgroup (PGL2 Nine.F)) (hD : Nat.card D = 10) :
    Nat.card (normalizer (D : Set (PGL2 Nine.F))) = 20 := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let S : Sylow 5 D := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity, hD]; decide +kernel
  have hi : (S : Subgroup D).index = 2 := by
    have hh := (S : Subgroup D).card_mul_index
    rw [hS, hD] at hh
    omega
  let : (S : Subgroup D).Normal := normal_of_index_eq_two hi
  let : (S : Subgroup D).Characteristic := S.characteristic_of_normal inferInstance
  let P := (S : Subgroup D).map D.subtype
  have hP : Nat.card P = 5 := (card_map_of_injective D.subtype_injective).trans hS
  let N := normalizer (P : Set (PGL2 Nine.F))
  have hN : Nat.card N = 20 := five_normalizer_card P hP
  have hDN : D ≤ N := by
    have hn := (S : Subgroup D).le_normalizer_map D.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  have hDi : (D.subgroupOf N).index = 2 := by
    have hh := (D.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv, hD, hN] at hh
    omega
  let : (D.subgroupOf N).Normal := normal_of_index_eq_two hDi
  have hNle : N ≤ normalizer (D : Set (PGL2 Nine.F)) := by
    have hn := (D.subgroupOf N).le_normalizer_map N.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_subgroupOf_eq_of_le hDN] at hn
    exact hn
  have hleN : normalizer (D : Set (PGL2 Nine.F)) ≤ N := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    let a := D.normalizerMonoidHom ⟨g, hg⟩
    have hfixed : (S : Subgroup D).comap a.toMonoidHom = S :=
      (inferInstance : (S : Subgroup D).Characteristic).fixed a
    have hay : a y ∈ (S : Subgroup D) := by
      change y ∈ (S : Subgroup D).comap a.toMonoidHom
      rwa [hfixed]
    exact mem_map.mpr ⟨a y, hay, rfl⟩
  rw [le_antisymm hleN hNle]
  exact hN

end AlternatingSix.PGLNineFiveNormalizer
