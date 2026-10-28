module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Surjective commutator rows in groups with center of order four

If an automorphism moves a commutator, some element has two distinct
nonidentity commutator values. Otherwise, choose an element outside the
two proper centralizers: uniqueness of the nonidentity value in each row,
and inversion on exchanging the two arguments, force the original and
transformed commutators to agree.

For a group of nilpotency class at most two, commutation with a fixed element
is a homomorphism into the center. If that center has order four, two distinct
nonidentity values make this homomorphism surjective.

This elementary argument supplies an alternative to the character-degree
count in Lyons, *A Characterization of the Group U₃(4)* (1972), p. 373.
-/

open scoped commutatorElement

namespace Subgroup

/-- If an automorphism moves a commutator, some commutator row contains two
 distinct nonidentity values. -/
public theorem exists_two_commutators_of_aut_moves
    {P : Type*} [Group P] (β : MulAut P) (a b : P)
    (hm : β ⁅a, b⁆ ≠ ⁅a, b⁆) :
    ∃ x y z : P, ⁅x, y⁆ ≠ 1 ∧ ⁅x, z⁆ ≠ 1 ∧ ⁅x, y⁆ ≠ ⁅x, z⁆ := by
  by_contra! hn
  have hrow (x y z : P) (hy : ⁅x,y⁆ ≠ 1) (hz : ⁅x,z⁆ ≠ 1) :
      ⁅x,y⁆ = ⁅x,z⁆ := hn x y z hy hz
  have hab : ⁅a,b⁆ ≠ 1 := by
    intro he
    exact hm (by simp [he])
  have hβab : ⁅β a, β b⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun he => hab (β.injective (he.trans β.map_one.symm))
  obtain ⟨z, hza, hzu⟩ : ∃ z : P,
      z ∉ centralizer ({a} : Set P) ∧ z ∉ centralizer ({β a} : Set P) := by
    by_contra! hcover
    have hh : (⊤ : Subgroup P) ≤ centralizer ({a} : Set P) ∨
        (⊤ : Subgroup P) ≤ centralizer ({β a} : Set P) :=
      SubgroupClass.subset_union.mp (fun z _ => or_iff_not_imp_left.mpr (hcover z))
    rcases hh with ha | hu
    · exact hab (commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_centralizer_singleton_iff.mp (ha (mem_top b))).symm))
    · exact hβab (commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_centralizer_singleton_iff.mp (hu (mem_top (β b)))).symm))
  have haz : ⁅a,z⁆ ≠ 1 := by
    intro he
    exact hza (mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm)
  have huz : ⁅β a,z⁆ ≠ 1 := by
    intro he
    exact hzu (mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm)
  have hza' : ⁅z,a⁆ ≠ 1 := by
    rw [← commutatorElement_inv a z, inv_ne_one]
    exact haz
  have hzu' : ⁅z,β a⁆ ≠ 1 := by
    rw [← commutatorElement_inv (β a) z, inv_ne_one]
    exact huz
  have he : ⁅a,z⁆ = ⁅β a,z⁆ := by
    simpa only [commutatorElement_inv] using congrArg Inv.inv (hrow z a (β a) hza' hzu')
  apply hm
  rw [map_commutatorElement, hrow (β a) (β b) z hβab huz, ← he,
    ← hrow a b z hab haz]

/-- The commutator with a fixed element, valued in the center of a group
of nilpotency class at most two. -/
@[expose] public def centerCommutatorHom {P : Type*} [Group P]
    (hc : _root_.commutator P ≤ center P) (x : P) : P →* center P where
  toFun y := ⟨⁅x,y⁆, hc (commutator_mem_commutator (mem_top x) (mem_top y))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := by
    apply Subtype.ext
    change ⁅x,y*z⁆ = ⁅x,y⁆ * ⁅x,z⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hz := mem_center_iff.mp
      (hc (commutator_mem_commutator (mem_top x) (mem_top z))) y
    calc
      _ = ⁅x,y⁆ * (y * ⁅x,z⁆) * y⁻¹ := by group
      _ = ⁅x,y⁆ * ⁅x,z⁆ := by rw [hz]; group

@[simp] public theorem centerCommutatorHom_apply {P : Type*} [Group P]
    (hc : _root_.commutator P ≤ center P) (x y : P) :
    (centerCommutatorHom hc x y : P) = ⁅x,y⁆ := rfl

public theorem centerCommutatorHom_ker {P : Type*} [Group P]
    (hc : _root_.commutator P ≤ center P) (x : P) :
    (centerCommutatorHom hc x).ker = centralizer ({x} : Set P) := by
  ext y
  change (⟨⁅x,y⁆, _⟩ : center P) = 1 ↔ _
  rw [Subtype.ext_iff]
  change ⁅x,y⁆ = 1 ↔ _
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff, eq_comm]

/-- Two distinct nonidentity commutator values fill a four-element center. -/
public theorem centerCommutatorHom_surjective_of_two_values
    {P : Type*} [Group P] [Finite P]
    (hc : _root_.commutator P ≤ center P) (hZ : Nat.card (center P) = 4)
    (x y z : P) (hy : ⁅x,y⁆ ≠ 1) (hz : ⁅x,z⁆ ≠ 1)
    (hyz : ⁅x,y⁆ ≠ ⁅x,z⁆) :
    Function.Surjective (centerCommutatorHom hc x) := by
  classical
  let f := centerCommutatorHom hc x
  let _ := Fintype.ofFinite f.range
  have hh : 2 < Nat.card f.range := by
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    refine ⟨1, ⟨f y, ⟨y, rfl⟩⟩, ⟨f z, ⟨z, rfl⟩⟩, ?_, ?_, ?_⟩
    · exact fun he => hy (congrArg (fun a : f.range => (a : center P).val) he).symm
    · exact fun he => hz (congrArg (fun a : f.range => (a : center P).val) he).symm
    · exact fun he => hyz (congrArg (fun a : f.range => (a : center P).val) he)
  have hd : Nat.card f.range ∣ 4 := hZ ▸ f.range.card_subgroup_dvd_card
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hn : Nat.card f.range ≠ 3 := by
    intro he
    rw [he] at hd
    norm_num at hd
  have hfull : Nat.card f.range = Nat.card (center P) := by rw [hZ]; omega
  exact f.range_eq_top.mp (f.range.eq_top_of_card_eq hfull)

end Subgroup
