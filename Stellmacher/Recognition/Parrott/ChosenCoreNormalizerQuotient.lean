module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterGeometry
public import Theory.GroupTheory.ElementaryEightWeaklyClosedPoint

/-!
# The chosen center as a small automizer

Let `S = C_G(z) ∩ C_G(a)` and suppose its center has order eight.
The faithful action of `N_G(S)/S` on this center has a two-element
subgroup whose fixed plane is its intersection with the derived core.
Derived weak closure says that the orbit of `z` meets that plane only
at `z`. Moreover, fixing both `z` and `a` makes an automorphism trivial,
since their common centralizer is exactly `S`.

These are the local inputs for the symmetric-three quotient assertion
in Parrott, *A characterization of the Tits' simple group* (1972), p.676.
The order-eight premise is kept separate from its proof.
The three-point orbit theorem identifies the action range, and the
first isomorphism theorem then identifies the actual normalizer quotient.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual chosen-center action has a weakly closed point in the fixed
plane of its derived involution, and a trivial two-point stabilizer. -/
private theorem chosen_center_small_automizer_data
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    let N := normalizer (S : Set G)
    IsElementaryAbelian 2 Z ∧ Nat.card Z = 8 ∧
    ∃ f : N →* MulAut Z,
      f.ker = S.subgroupOf N ∧
      Nonempty ((N ⧸ S.subgroupOf N) ≃* f.range) ∧
      Group.IsSolvable f.range ∧
      ∃ B : Subgroup (MulAut Z), B ≤ f.range ∧ Nat.card B = 2 ∧
      ∃ W : Subgroup Z, Nat.card W = 4 ∧
      ∃ z₀ a₀ : Z, (z₀ : G) = z ∧ (a₀ : G) = (d.a : G) ∧
        z₀ ≠ 1 ∧ a₀ ≠ 1 ∧ a₀ ≠ z₀ ∧ z₀ ∈ W ∧
        (∀ v : Z, (∀ b ∈ B, b v = v) ↔ v ∈ W) ∧
        (∀ v ∈ MulAction.orbit f.range z₀, v ∈ W → v = z₀) ∧
        (∃ g : f.range, g • z₀ ≠ z₀) ∧
        (∀ g ∈ f.range, g z₀ = z₀ → g a₀ = a₀ → g = 1) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  let N := normalizer (S : Set G)
  let : IsElementaryAbelian 2 (center S) := d.chosen_center_elementary
  have hZelem : IsElementaryAbelian 2 Z := IsElementaryAbelian.map S.subtype
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective S.subtype_injective).trans hcenter
  refine ⟨hZelem, hZcard, ?_⟩
  obtain ⟨f, hf, hker, hequiv⟩ := d.chosen_center_action
  let : Group.IsSolvable N := d.chosen_centralizer_normalizer_solvable h hN
  have hsolv : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  let B := (E.subgroupOf N).map f
  let W := E.subgroupOf Z
  have hBcard : Nat.card B = 2 := d.chosen_center_derived_action_card h f hker
  have hWcard : Nat.card W = 4 := by
    have hc := (d.chosen_center_derived_index).2
    change Nat.card Z = 2 * Nat.card (E ⊓ Z : Subgroup G) at hc
    have hw : Nat.card W = Nat.card (E ⊓ Z : Subgroup G) := by
      change Nat.card (E.subgroupOf Z) = _
      rw [← inf_subgroupOf_right E Z]
      exact Nat.card_congr
        (subgroupOfEquivOfLe (show E ⊓ Z ≤ Z from inf_le_right)).toEquiv
    rw [hZcard] at hc
    omega
  let z₀ : Z := ⟨z, d.chosen_centralizer_center.1⟩
  let a₀ : Z := ⟨d.a, d.chosen_centralizer_center.2.1⟩
  have haE : (d.a : G) ∉ E := by
    rintro ⟨b, hb, heq⟩
    exact d.a_not_mem_derived ⟨b, hb, H.subtype_injective heq⟩
  have hz1 : z₀ ≠ 1 := by
    intro hz
    have heq : z = 1 := congrArg Subtype.val hz
    have ho := h.involution
    simp [heq] at ho
  have ha1 : a₀ ≠ 1 := by
    intro ha
    exact haE ((congrArg Subtype.val ha).symm ▸ E.one_mem)
  have haz : a₀ ≠ z₀ := by
    intro heq
    exact haE ((congrArg Subtype.val heq).symm ▸ d.z_mem_inf.1)
  have hzW : z₀ ∈ W := d.z_mem_inf.1
  have hEN : E ≤ N := d.derived_le_chosen_centralizer_normalizer h
  have hCE : centralizer (E : Set G) = E := parrott_derived_centralizer z h
  have hfix (v : Z) : (∀ b ∈ B, b v = v) ↔ v ∈ W := by
    constructor
    · intro hv
      change (v : G) ∈ E
      rw [← hCE]
      intro e he
      have hfv := congrArg Subtype.val (hv (f ⟨e, hEN he⟩)
        (mem_map_of_mem f (show (⟨e, hEN he⟩ : N) ∈ E.subgroupOf N from he)))
      rw [hf] at hfv
      exact mul_inv_eq_iff_eq_mul.mp hfv
    · intro hv b hb
      obtain ⟨e, he, rfl⟩ := hb
      apply Subtype.ext
      rw [hf]
      have hc : (v : G) ∈ centralizer (E : Set G) :=
        hCE.symm ▸ hv
      rw [hc e he, mul_inv_cancel_right]
  have hinter (v : Z) (hv : v ∈ MulAction.orbit f.range z₀) (hvW : v ∈ W) :
      v = z₀ := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hv
    obtain ⟨n, hn⟩ := g.property
    have hval : (v : G) = (n : G) * z * (n : G)⁻¹ := by
      rw [← hg]
      change ((g : MulAut Z) z₀ : G) = _
      rw [← hn, hf]
    apply Subtype.ext
    exact hderived _ hvW (isConj_iff.mpr ⟨n, hval.symm⟩)
  have hmove : ∃ g : f.range, g • z₀ ≠ z₀ := by
    by_contra! hfixed
    apply d.chosen_centralizer_normalizer_not_le h hconj
    intro n hn
    have hh := congrArg Subtype.val (hfixed (f.rangeRestrict ⟨n, hn⟩))
    change (f ⟨n, hn⟩ z₀ : G) = z at hh
    rw [hf] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  have hpair (g : MulAut Z) (hg : g ∈ f.range) (hgz : g z₀ = z₀)
      (hga : g a₀ = a₀) : g = 1 := by
    obtain ⟨n, rfl⟩ := hg
    have hnS : n ∈ S.subgroupOf N := by
      constructor
      · have hh := congrArg Subtype.val hgz
        rw [hf] at hh
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
      · have hh := congrArg Subtype.val hga
        rw [hf] at hh
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
    exact (MonoidHom.mem_ker.mp (hker.symm ▸ hnS))
  exact ⟨f, hker, hequiv, hsolv, B, map_le_range f _, hBcard,
    W, hWcard, z₀, a₀, rfl, rfl, hz1, ha1, haz, hzW, hfix, hinter, hmove, hpair⟩

/-- Given the order-eight center, the actual normalizer quotient is S3.
The original simple nonsolvable N₂ hypotheses and supplied self-normalized
fixed join are retained; the counting argument needs only the displayed
local action consequences of these hypotheses. -/
public theorem chosen_centralizer_normalizer_quotient [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (_hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let N := normalizer (S : Set G)
    Nonempty ((N ⧸ S.subgroupOf N) ≃* Equiv.Perm (Fin 3)) := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  obtain ⟨hZelem, hZcard, f, _, ⟨e⟩, hsolv, B, hBA, hBcard, W, hWcard,
    z₀, a₀, _, _, hz1, ha1, haz, hzW, hfix, hinter, hmove, hpair⟩ :=
    d.chosen_center_small_automizer_data h hN hconj hderived hcenter
  let : IsElementaryAbelian 2 Z := hZelem
  let : Group.IsSolvable f.range := hsolv
  obtain ⟨e'⟩ := elementaryEight_automizer_equiv_perm_three hZcard f.range B hBA
    hBcard W hWcard z₀ a₀ hz1 ha1 haz hzW hfix hinter hmove hpair
  exact ⟨e.trans e'⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
