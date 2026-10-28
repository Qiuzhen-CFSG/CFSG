module

public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Elementary rank and the center of the ordinary point component

The original elementary subgroup has order 64. A quotient of two-rank at
most four therefore kills at least four of its elements. In particular,
a cyclic center cannot be the kernel of such a quotient. This supplies the
center obstruction without assuming that the original field point is
already central in the ordinary component.

Source: Aschbacher--Smith, 12.7.5, printed p.840.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section07
variable {B S : Type*} [Group B] [Finite B] [Group S] [Finite S]

omit [Finite B] in
/-- An elementary subgroup of order 64 loses at least a four-group in a
homomorphism to a group of two-rank at most four. -/
theorem original_point_four_le_card_kernel
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (q : B →* S) (hr : primeRank 2 S ≤ 4) :
    4 ≤ Nat.card (U ⊓ q.ker : Subgroup B) := by
  have hm : Nat.card (U.map q) ≤ 16 :=
    (primeRank_le_iff_elementary_card_le S).mp hr _ (IsElementaryAbelian.map q)
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map U q
  rw [hU] at hh
  nlinarith

omit [Finite B] in
/-- A cyclic center is incompatible with the original elementary subgroup
of order 64 when the central quotient has two-rank at most four. -/
theorem original_point_center_not_isCyclic
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (e : B ⧸ center B ≃* S) (hr : primeRank 2 S ≤ 4) :
    ¬ IsCyclic (center B) := by
  intro hc
  let : IsCyclic (center B) := hc
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hq : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hbig := original_point_four_le_card_kernel U hU q hr
  rw [hq] at hbig
  let E : Subgroup B := U ⊓ center B
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left)
      (inclusion_injective inf_le_left)
  let : IsCyclic E := isCyclic_of_injective (inclusion inf_le_right)
    (inclusion_injective inf_le_right)
  have hd : Nat.card E ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 E
  have hsmall := Nat.le_of_dvd (by decide : 0 < 2) hd
  change 4 ≤ Nat.card E at hbig
  omega

/-- A known four-group containing the central intersection is exactly the
central intersection. Thus its centrality follows from the quotient rank. -/
theorem original_point_inf_center_eq_of_rank_four
    (U V : Subgroup B) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 64) (hV : Nat.card V = 4)
    (e : B ⧸ center B ≃* S) (hr : primeRank 2 S ≤ 4)
    (hUV : U ⊓ center B ≤ V) : U ⊓ center B = V := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hq : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hbig := original_point_four_le_card_kernel U hU q hr
  rw [hq] at hbig
  exact eq_of_le_of_card_ge hUV (hV ▸ hbig)

end CFSG.Quasithin.Chapter12.Section07
