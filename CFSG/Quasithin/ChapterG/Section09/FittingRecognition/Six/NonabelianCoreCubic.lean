module
public import Theory.Representation.NormalNineDegreeSix
public import Theory.GroupTheory.PGroup.Omega
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.CoreRank

/-!
# A normal cubic from a small nonabelian three-core

A nonabelian three-group of order at most 81 has center of order at most
nine: a smaller central quotient would be cyclic and force commutativity.
The first omega subgroup of its center is therefore a nontrivial
characteristic elementary subgroup of order three or nine.

Its ambient image is normal. At order three this is the desired subgroup;
at order nine the faithful irreducible degree-six representation supplies
an ambient-normal cubic through the four cubic fixed spaces. This avoids
recognizing a Sylow subgroup of GL₆(2) or a full linear normalizer.

The final application retains the literal G.9 Fitting representation
and discharges the order bound on its actual three-core with the
degree-six finite linear order calculation.

Source: Aschbacher--Smith G.9.4(5), printed p.355.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six

private theorem center_card_le_nine {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 3 P) (hc : Nat.card P ≤ 81) (hne : ¬ IsMulCommutative P) :
    Nat.card (center P) ≤ 9 := by
  obtain ⟨a,ha⟩ := (hp.to_quotient (center P)).exists_card_eq
  have ha2 : 2 ≤ a := by
    by_contra h
    have hd : Nat.card (P ⧸ center P) ∣ 3 := by
      rw [ha]
      have he : a = 0 ∨ a = 1 := by omega
      rcases he with rfl | rfl <;> simp
    let : IsCyclic (P ⧸ center P) := isCyclic_of_card_dvd_prime hd
    exact hne (isMulCommutative_of_isCyclic_quotient_center_self P)
  have hq : 9 ≤ (center P).index := by
    rw [index_eq_card,ha]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) ha2
  have hm := (center P).card_mul_index
  nlinarith

/-- The central omega subgroup suffices for the nonabelian three-core case. -/
theorem normal_cubic_of_nonabelian_threeCore_le_81
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    [Representation.IsIrreducible ρ] (hd : finrank (ZMod 2) V = 6)
    (hc : Nat.card (pCore 3 G) ≤ 81) (hne : ¬ IsMulCommutative (pCore 3 G)) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let B := pCore 3 G
  have hp : IsPGroup 3 B := pCore_isPGroup
  let : Nontrivial B := not_subsingleton_iff_nontrivial.mp (fun hs => by
    let := hs
    exact hne inferInstance)
  let : Nontrivial (center B) := hp.center_nontrivial
  let O := omega₁ (center B) (p := 3)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 3 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center B).subtype
  let : Z.Characteristic := inferInstance
  let N := Z.map B.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 3 N := IsElementaryAbelian.map_subtype
  have hbound : Nat.card O ≤ 9 :=
    (card_le_card_group O).trans (center_card_le_nine hp hc hne)
  have hdiv : 3 ∣ Nat.card (center B) :=
    (hp.to_subgroup _).card_eq_or_dvd.resolve_left (Nat.ne_of_gt Finite.one_lt_card)
  have hnb := omega₁_map_subtype_ne_bot (center B) 3 hdiv
  have hone : Nat.card O ≠ 1 := by
    intro he
    have hb : O = ⊥ := card_eq_one.mp he
    exact hnb (by rw [show omega₁ (center B) (p := 3) = ⊥ from hb, Subgroup.map_bot])
  obtain ⟨a,ha⟩ := ((hp.to_subgroup (center B)).to_subgroup O).exists_card_eq
  have hale : a ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    simpa [← ha] using hbound
  have ha0 : a ≠ 0 := by intro he; exact hone (by simpa [he] using ha)
  have hN : Nat.card N = Nat.card O := by
    rw [card_map_of_injective B.subtype_injective,card_map_of_injective (center B).subtype_injective]
  have he : a = 1 ∨ a = 2 := by omega
  rcases he with he | he
  · exact ⟨N,inferInstance,by rw [hN,ha,he]; decide⟩
  · obtain ⟨C,_,hCn,hCc⟩ :=
      Representation.NormalNineDegreeSix.exists_normal_cubic_of_irreducible ρ hf N
        (by rw [hN,ha,he]; decide) hd
    exact ⟨C,hCn,hCc⟩

/-- The exact source Fitting representation consumes the nonabelian-core branch. -/
theorem normal_cubic_of_source_nonabelian_threeCore_le_81
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2) (hd : finrank (ZMod 2) V = 6)
    (hc : Nat.card (pCore 3 G) ≤ 81) (hne : ¬ IsMulCommutative (pCore 3 G)) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let := h.irreducible
  exact normal_cubic_of_nonabelian_threeCore_le_81 ρ h.faithful hd hc hne

/-- The original degree-six Fitting hypothesis supplies the core order bound. -/
theorem normal_cubic_of_source_nonabelian_threeCore
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2) (hd : finrank (ZMod 2) V = 6)
    (hne : ¬ IsMulCommutative (pCore 3 G)) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 :=
  normal_cubic_of_source_nonabelian_threeCore_le_81 h hd
    (source_six_threeCore_card_le_eightyone h hd) hne

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
