module

public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.SpecificGroups.PSL2.RankOneRoots

/-!
# Small binary PSL₂ inner centralizers

The full element centralizer is a conjugate root group of order 2ⁿ.
If its order divides 2304, then n ≤ 8. The inner centralizer is a
two-group, while the actual outer group has order n, which is nine-free.
Source: Aschbacher--Smith 14.3.20, printed p.998, the binary PSL₂ row.
-/

public section
open Subgroup
namespace Theory.PSL2
open BenderSuzuki.Converse
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Root geometry computes the full centralizer of every binary involution. -/
theorem binary_involution_centralizer_card (x : Group F) (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set (Group F))) = Nat.card F := by
  obtain ⟨g, t, ht, hg, _, _⟩ := involution_root_geometry x hx
  rw [Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) x).toEquiv,
    hg, centralizer_root_eq ht]
  exact PUnip_card

/-- The small-centralizer restriction gives the required full automorphism bound. -/
theorem binary_not_nine_dvd_inner_involution_centralizer {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (x : Group F) (hx : orderOf x = 2)
    (hc : Nat.card (centralizer ({x} : Set (Group F))) ∣ 2304) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (Group F)))) := by
  have hc' : 2 ^ n ∣ 2304 := by rwa [binary_involution_centralizer_card x hx, hF] at hc
  have hn : n ≤ 8 := by
    by_contra h
    have hd : 512 ∣ 2304 := (Nat.pow_dvd_pow 2 (show 9 ≤ n by omega)).trans hc'
    norm_num at hd
  have hz : center (Group F) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have h := (centerCongr (sl2QuotientEquiv F).symm ⟨z, hz⟩).property
    have h1 := (sl2_center_eq_bot F).le h
    have he := congrArg (sl2QuotientEquiv F) (mem_bot.mp h1)
    simpa using he
  have hd := MulAut.centralizer_conj_card_dvd hz x
  rw [binary_involution_centralizer_card x hx, hF, outer_card_eq_field_degree F hF] at hd
  intro h9
  have hd9 : 9 ∣ n := ((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left
    (h9.trans hd)
  have hn0 : n ≠ 0 := by
    intro he
    have hb : 1 < Nat.card F := Finite.one_lt_card
    rw [hF, he] at hb
    norm_num at hb
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd9
  omega

end Theory.PSL2
