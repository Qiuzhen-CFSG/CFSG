module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightData
public import Theory.GroupTheory.NormalClosureSylowActionCore

/-!
# The two-core of the separated closure action

The central omega identity in the local setup says that the four generating
the closure is centralized by the local Sylow subgroup. The general normal
closure action lemma therefore makes the conjugation image on the closure
two-core-free. No order-eight or solvability hypothesis is needed here.

This is the first automizer reduction in Janko–Thompson, Math. Z. 113
(1970), Lemma 3.1, printed pp.387–388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The local supplement's actual action on its elementary closure has
trivial two-core. -/
public theorem closure_action_twoCore_eq_bot {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) :
    pCore 2 (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range = ⊥ := by
  let P := d.T.subtype d.sylow_le
  let Z := ((W.map (S : Subgroup G).subtype).subgroupOf
    (centralizer ({(i : G)} : Set G))).subgroupOf d.H
  apply pCore_conjNormal_range_eq_bot_of_normalClosure P Z d.closure rfl
  intro z hz t ht
  have hzU : (z : centralizer ({(i : G)} : Set G)) ∈
      (W.map (S : Subgroup G).subtype).subgroupOf
        (centralizer ({(i : G)} : Set G)) := hz
  rw [← d.omega_center_eq] at hzU
  obtain ⟨zT, hzT, he⟩ := hzU
  have hzcenter : zT ∈ center d.T := map_subtype_le _ hzT
  have hc := mem_center_iff.mp hzcenter (⟨t.val, ht⟩ : d.T)
  apply Subtype.ext
  change (t : centralizer ({(i : G)} : Set G)) * z =
    (z : centralizer ({(i : G)} : Set G)) * t
  rw [← he]
  exact congrArg Subtype.val hc

/-- An order-eight closure has a nontrivial Sylow action: otherwise it
would be contained in the prescribed central omega, which has order four. -/
public theorem two_dvd_card_closure_action {S : Sylow 2 G} {W : Subgroup S}
    (hW : Nat.card W = 4) {i : S} (d : CentralizerSetup S W i)
    (hc : Nat.card d.closure = 8) :
    2 ∣ Nat.card (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range := by
  let f : d.H →* MulAut d.closure := MulAut.conjNormal
  let P := d.T.subtype d.sylow_le
  let Q := P.mapSurjective f.rangeRestrict_surjective
  by_contra hodd
  have hQbot : (Q : Subgroup f.range) = ⊥ := by
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      apply hodd
      apply dvd_trans ?_ Q.toSubgroup.card_subgroup_dvd_card
      rw [hn]
      exact dvd_pow_self 2 hn0
    apply card_eq_one.mp
    rw [hn, hn0, pow_zero]
  have htrivial (t : d.T) : f ⟨t, d.sylow_le t.property⟩ = 1 := by
    have hh : f.rangeRestrict ⟨t, d.sylow_le t.property⟩ ∈ (Q : Subgroup f.range) :=
      mem_map_of_mem _ t.property
    rw [hQbot] at hh
    exact congrArg Subtype.val (mem_bot.mp hh)
  let C := centralizer ({(i : G)} : Set G)
  let U := (W.map (S : Subgroup G).subtype).subgroupOf C
  have hle : d.closure.map d.H.subtype ≤ U := by
    rintro _ ⟨e, he, rfl⟩
    let eT : d.T := ⟨e, d.closure_le (mem_map_of_mem _ he)⟩
    have hecenter : eT ∈ center d.T := by
      apply mem_center_iff.mpr
      intro t
      have hh := congrArg (fun a : MulAut d.closure =>
        ((a ⟨e, he⟩ : d.closure) : d.H)) (htrivial t)
      change (⟨t, d.sylow_le t.property⟩ : d.H) * e *
        (⟨t, d.sylow_le t.property⟩ : d.H)⁻¹ = e at hh
      have hh' := congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hh)
      exact Subtype.ext hh'
    have he2 : eT ^ 2 = 1 := by
      let : IsElementaryAbelian 2 d.closure := d.elementary
      apply Subtype.ext
      change (e : C) ^ 2 = 1
      exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := 2) e he)
    have heomega : (⟨eT, hecenter⟩ : center d.T) ∈ omega₁ (center d.T) (p := 2) := by
      apply Subgroup.subset_closure
      change (⟨eT, hecenter⟩ : center d.T) ^ (2 ^ 1) = 1
      apply Subtype.ext
      simpa using he2
    dsimp only [U, C]
    rw [← d.omega_center_eq]
    exact mem_map_of_mem _ (mem_map_of_mem _ heomega)
  have hle' : (d.closure.map d.H.subtype).map C.subtype ≤
      W.map (S : Subgroup G).subtype := by
    rintro _ ⟨e, he, rfl⟩
    exact hle he
  have hcard := card_le_of_le hle'
  rw [card_map_of_injective C.subtype_injective,
    card_map_of_injective d.H.subtype_injective,
    card_map_of_injective (S : Subgroup G).subtype_injective, hc, hW] at hcard
  omega

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
