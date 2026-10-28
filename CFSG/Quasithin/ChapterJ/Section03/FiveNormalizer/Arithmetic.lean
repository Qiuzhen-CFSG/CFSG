module
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
/-!
# The elementary-five normalizer order in J.3.6

A self-centralizing elementary group of order125 makes its normalizer act
faithfully modulo that group in GL₃(5). Intersecting its resulting order
bound with the actual Ru order and the exact two-part leaves orders4000
and12000. The Sylow congruence modulo625 excludes12000.

This uses the concrete matrix-group cardinality and divisibility alone.
The exact two-part is the separate local wreath-group construction.
Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03

private theorem five_normalizer_arithmetic (n : ℕ)
    (hG : n ∣ 2^14*3^3*5^3*7*13*29) (hGL : n ∣ 125*1488000)
    (h125 : 125∣n) (h32 : 32∣n) (h64 : ¬64∣n)
    (hm : Nat.ModEq (5^4) n (2^14*3^3*5^3*7*13*29)) : n=4000 := by
  have hd : n∣48000 := Nat.dvd_gcd hG hGL
  have h4000 : 4000∣n :=
    (show Nat.Coprime 125 32 by decide).mul_dvd_of_dvd_of_dvd h125 h32
  obtain ⟨k,rfl⟩ := h4000
  have hk : k∣12 := (Nat.mul_dvd_mul_iff_left (by decide : 0<4000)).mp hd
  have hb : k≤12 := Nat.le_of_dvd (by decide) hk
  interval_cases k <;> norm_num [Nat.ModEq] at *

variable {G : Type*} [Group G] [Finite G]

theorem five_normalizer_order_of_elementary_selfcentralizer
    (hG : Nat.card G = 2^14*3^3*5^3*7*13*29)
    (P : Subgroup G) [IsElementaryAbelian 5 P]
    (hP : Nat.card P=125) (hC : centralizer (P : Set G)=P)
    (h32 : 32∣Nat.card (normalizer (P : Set G)))
    (h64 : ¬64∣Nat.card (normalizer (P : Set G))) :
    Nat.card (normalizer (P : Set G))=4000 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=5) (n:=3) P (by rw [hP]; decide)
  have hGLcard : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 5))=1488000 := by
    rw [Matrix.card_GL_field]
    norm_num [Nat.card_zmod,Fin.prod_univ_succ]
  have haut : Nat.card (MulAut P)∣1488000 := hGLcard ▸ card_dvd_of_injective f hf
  have hker : Nat.card P.normalizerMonoidHom.ker = 125 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (P : Set G))).toEquiv,
      hC,hP]
  have he := P.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hker] at he
  have hdiv : Nat.card (normalizer (P : Set G)) ∣ 125*1488000 := by
    rw [← he]
    exact Nat.mul_dvd_mul_left _ (P.normalizerMonoidHom.range.card_subgroup_dvd_card.trans haut)
  have hdG : Nat.card (normalizer (P : Set G))∣2^14*3^3*5^3*7*13*29 :=
    hG ▸ (normalizer (P : Set G)).card_subgroup_dvd_card
  have h125 : 125∣Nat.card (normalizer (P : Set G)) := hP ▸ card_dvd_of_le P.le_normalizer
  have hm := Sylow.card_normalizer_modEq_card (p:=5) (n:=3) hP
  rw [hG] at hm
  exact five_normalizer_arithmetic _ hdG hdiv h125 h32 h64 hm

end CFSG.Quasithin.ChapterJ.Section03
