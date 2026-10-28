module

public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.GroupTheory.Commutator.CentralizingFactor
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Invariance of a maximum elementary replacement commutator

If the A-commutator of B centralizes Y, its relative centralizer is
A-invariant. A conjugate of Y commuting with Y then lies in the maximum
elementary replacement Y C_B(Y), forcing invariance of [B,Y].
This is the maximum-order argument in Campbell II.7.6, pp.35–36.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem centralizer_factor_normalized (A B Y : Subgroup H)
    (hAB : ⁅A,B⁆ ≤ B ⊓ centralizer (Y : Set H)) :
    A ≤ normalizer ((B ⊓ centralizer (Y : Set H) : Subgroup H) : Set H) := by
  apply le_normalizer_iff.mpr
  intro x hx b hb
  have hc := hAB (commutator_mem_commutator hx hb.1)
  have hm := (B ⊓ centralizer (Y : Set H)).mul_mem hc hb
  simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm

theorem commutator_normalized_of_commuting_conjugate (S A B Y : Subgroup H)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 Y]
    (hAB : ⁅A,B⁆ ≤ B ⊓ centralizer (Y : Set H))
    (hW : Y ⊔ (B ⊓ centralizer (Y : Set H)) ∈ elementaryAbelianMaxSubgroups S)
    (x : H) (hx : x ∈ A)
    (hYxS : Y.map (MulAut.conj x).toMonoidHom ≤ S)
    (hYYx : ⁅Y,Y.map (MulAut.conj x).toMonoidHom⁆=⊥) :
    x ∈ normalizer ((⁅B,Y⁆ : Subgroup H) : Set H) := by
  let D := B ⊓ centralizer (Y : Set H)
  let W := Y ⊔ D
  let Yx := Y.map (MulAut.conj x).toMonoidHom
  have hBN : A ≤ normalizer (B : Set H) := le_normalizer_iff_commutator_le_right.mpr (hAB.trans inf_le_left)
  have hDN : A ≤ normalizer (D : Set H) := centralizer_factor_normalized A B Y hAB
  have hDx : D.map (MulAut.conj x).toMonoidHom=D := mem_normalizer_iff_map_conj_eq.mp (hDN hx)
  have hDYx : D ≤ centralizer (Yx : Set H) := by
    rw [←hDx]
    exact (map_mono (show D ≤ centralizer (Y : Set H) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ _)
  have hYxW : Yx ≤ centralizer (W : Set H) := by
    apply le_centralizer_iff.mpr
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hYYx) hDYx
  let : IsElementaryAbelian 2 Yx := IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hYx : Yx ≤ W := maxElementary_contains_elementary_centralizer S W Yx hW hYxS hYxW
  have hWx : W.map (MulAut.conj x).toMonoidHom ≤ W := by
    change (Y ⊔ D).map _ ≤ _
    rw [Subgroup.map_sup,hDx]
    exact sup_le hYx le_sup_right
  have hWeq : W.map (MulAut.conj x).toMonoidHom=W :=
    Subgroup.eq_of_le_of_card_ge hWx (by rw [Subgroup.card_map_of_injective (K:=W) (MulAut.conj x).injective])
  have hBW : ⁅B,W⁆=⁅B,Y⁆ := by
    apply commutator_eq_of_product_centralizing_factor
      (coe_mul_of_left_le_normalizer_right Y D
        ((le_centralizer_iff.mp (show D ≤ centralizer (Y : Set H) from inf_le_right)).trans
          (Subgroup.centralizer_le_normalizer _)))
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show D ≤ B from inf_le_left))
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [←hBW,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hBN hx)]
  change ⁅B,W.map (MulAut.conj x).toMonoidHom⁆=⁅B,W⁆
  rw [hWeq]

end Subgroup
