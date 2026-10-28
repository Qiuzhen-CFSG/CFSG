module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Transfer
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import BenderSuzuki.PFAppendixIII.Basic
public import Theory.GroupTheory.PGroup.Omega

/-!
# The Suzuki two-group geometry used by J.2.9

The nonabelian moving factor has a nontrivial derived subgroup inside V.
The seven-group orbit on V makes this derived subgroup all of V. The
regular involution action in the definition of a Suzuki two-group then
puts every involution in that characteristic subgroup. Consequently V
is exactly Ω₁(S₁), and every involution of the local direct product is
central. This proves the geometry required by transfer, rather than
assuming a square-one description of S₁.

Source: Aschbacher–Smith, J.2.3(3),(5) and the first paragraph of the
proof of J.2.9, printed pp.433–434,438.
-/

@[expose] public section
noncomputable section
open Subgroup
open BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- The literal Singer conjugation orbit used in the proof of J.2.3. -/
def B7TransitiveOnV : Prop :=
  ∀ v ∈ d.V, v ≠ 1 → ∀ w ∈ d.V, w ≠ 1 →
    ∃ b ∈ c.B7, b * v * b⁻¹ = w

/-- Nonabelianity and the Singer orbit identify the derived subgroup. -/
theorem S1_derived_eq_V (hnonab : ¬ IsMulCommutative c.S1)
    (htrans : c.B7TransitiveOnV) :
    (_root_.commutator c.S1).map c.S1.subtype = d.V := by
  let D := (_root_.commutator c.S1).map c.S1.subtype
  have hle : D ≤ d.V := by
    dsimp only [D]
    rw [← d.ru1.derived_eq, map_subtype_commutator, map_subtype_commutator]
    exact commutator_mono (c.S1_le_Ts.trans inf_le_left) (c.S1_le_Ts.trans inf_le_left)
  have hne : D ≠ ⊥ := by
    intro h
    have hbot := ((_root_.commutator c.S1).map_eq_bot_iff_of_injective
      c.S1.subtype_injective).mp h
    exact hnonab ((commutator_eq_bot_iff c.S1).mp hbot)
  have hn : c.B7 ≤ normalizer (D : Set G) :=
    (normalizer_commutator_ge_right c.Ts c.B7).trans
      (normalizer_le_normalizer_characteristic_image c.S1 (_root_.commutator c.S1))
  obtain ⟨⟨v, hv⟩, hv1⟩ := ne_bot_iff_exists_ne_one.mp hne
  apply le_antisymm hle
  intro w hw
  by_cases hw1 : w = 1
  · exact hw1 ▸ D.one_mem
  obtain ⟨b, hb, he⟩ := htrans v (hle hv)
    (fun h => hv1 (Subtype.ext h)) w hw hw1
  exact he ▸ (hn hb v).mp hv

theorem Ts_derived_eq_V (hnonab : ¬ IsMulCommutative c.S1)
    (htrans : c.B7TransitiveOnV) :
    (_root_.commutator c.Ts).map c.Ts.subtype = d.V := by
  apply le_antisymm
  · rw [← d.ru1.derived_eq, map_subtype_commutator, map_subtype_commutator]
    exact commutator_mono inf_le_left inf_le_left
  · rw [← c.S1_derived_eq_V hnonab htrans, map_subtype_commutator,
      map_subtype_commutator]
    exact commutator_mono c.S1_le_Ts c.S1_le_Ts

theorem V_le_S1 (hnonab : ¬ IsMulCommutative c.S1)
    (htrans : c.B7TransitiveOnV) : d.V ≤ c.S1 := by
  rw [← c.S1_derived_eq_V hnonab htrans]
  exact map_subtype_le _

/-- The Suzuki involution action gives the square-one description, with
the ambient V identified by its derived subgroup. -/
theorem mem_V_iff_S1_square_one (hsuzuki : IsSuzukiTwoGroup c.S1)
    (htrans : c.B7TransitiveOnV) (x : G) :
    x ∈ d.V ↔ x ∈ c.S1 ∧ x ^ 2 = 1 := by
  have hD := c.S1_derived_eq_V hsuzuki.2.1 htrans
  constructor
  · intro hx
    exact ⟨c.V_le_S1 hsuzuki.2.1 htrans hx,
      congrArg Subtype.val (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨x, hx⟩)⟩
  · rintro ⟨hx, hx2⟩
    by_cases hx1 : x = 1
    · exact hx1 ▸ d.V.one_mem
    have hne : _root_.commutator c.S1 ≠ ⊥ := by
      intro h
      exact hsuzuki.2.1 ((commutator_eq_bot_iff c.S1).mp h)
    obtain ⟨⟨v, hv⟩, hv1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hvV : (v : G) ∈ d.V := hD ▸ mem_map_of_mem c.S1.subtype hv
    have hv2 : v ^ 2 = 1 := by
      apply Subtype.ext
      change (v : G) ^ 2 = 1
      exact congrArg (fun w : d.V => (w : G))
        (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨v, hvV⟩)
    obtain ⟨K, hK, hact, _, _, hreg⟩ := hsuzuki.2.2.2
    let := hK
    let := hact
    obtain ⟨k, hk, _⟩ := hreg.2 v
      ⟨fun h => hv1 (Subtype.ext h), hv2⟩ (⟨x, hx⟩ : c.S1)
      ⟨fun h => hx1 (congrArg Subtype.val h), Subtype.ext hx2⟩
    let α : MulAut c.S1 := MulDistribMulAction.toMulAut K c.S1 k
    have hα : α v ∈ _root_.commutator c.S1 :=
      (characteristic_iff_map_le.mp inferInstance α) (mem_map_of_mem α.toMonoidHom hv)
    change k • v ∈ _root_.commutator c.S1 at hα
    rw [← hk] at hα
    exact hD ▸ mem_map_of_mem c.S1.subtype hα

/-- The literal first omega subgroup, mapped into G, is V. -/
theorem omega_S1_eq_V (hsuzuki : IsSuzukiTwoGroup c.S1)
    (htrans : c.B7TransitiveOnV) :
    (omega₁ c.S1 (p := 2)).map c.S1.subtype = d.V := by
  have he : omega₁ c.S1 (p := 2) = d.V.subgroupOf c.S1 := by
    apply le_antisymm
    · apply (Subgroup.closure_le (K := d.V.subgroupOf c.S1)).mpr
      intro x hx
      exact (c.mem_V_iff_S1_square_one hsuzuki htrans x).mpr
        ⟨x.property, congrArg Subtype.val (show x ^ 2 = 1 from by simpa using hx)⟩
    · intro x hx
      apply Subgroup.subset_closure
      change x ^ (2 ^ 1) = 1
      exact Subtype.ext ((c.mem_V_iff_S1_square_one hsuzuki htrans x).mp hx).2
  rw [he, map_subgroupOf_eq_of_le (c.V_le_S1 hsuzuki.2.1 htrans)]

/-- In the actual product, the elementary factor centralizes the whole
Sylow group, and all Sylow involutions are central. -/
theorem local_product_transfer_geometry [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV) :
    c.S0 ≤ centralizer (c.Ts : Set G) ∧
      ∀ x : P, x ^ 2 = 1 → (x : c.Gs) ∈ centralizer (P : Set c.Gs) := by
  let : CommGroup c.S0 := IsMulCommutative.instCommGroup
  have hcentral : c.S0 ≤ centralizer (c.Ts : Set G) := by
    intro a ha t ht
    let tG : c.Gs := ⟨t, (show c.Ts ≤ c.Gs from inf_le_right) ht⟩
    let tP : P := ⟨tG, by change tG ∈ (P : Subgroup c.Gs); rw [hP]; exact ht⟩
    let a0 : c.S0 := ⟨a, ha⟩
    let aP := e.symm (a0, 1)
    have haG : ((aP : c.Gs) : G) = a := by simpa [aP, a0] using he aP
    have hcomm : aP * tP = tP * aP := by
      apply e.injective
      simp only [map_mul, aP, e.apply_symm_apply]
      exact Prod.ext (mul_comm _ _) (by simp)
    have hh := congrArg (fun x : P => ((x : c.Gs) : G)) hcomm
    change ((aP : c.Gs) : G) * t = t * ((aP : c.Gs) : G) at hh
    simpa only [haG] using hh.symm
  refine ⟨hcentral, ?_⟩
  intro x hx
  have hb2 : (e x).2 ^ 2 = 1 := by
    have hh := congrArg (fun y : P => (e y).2) hx
    simpa using hh
  have hbV : ((e x).2 : G) ∈ d.V :=
    (c.mem_V_iff_S1_square_one hsuzuki htrans _).mpr
      ⟨(e x).2.property, congrArg Subtype.val hb2⟩
  have hxc : ((x : c.Gs) : G) ∈ centralizer (c.Ts : Set G) := by
    rw [he]
    apply mul_mem (hcentral (e x).1.property)
    intro t ht
    exact d.ru1.central_V hbV t ht.1
  intro y hy
  have hyT : (y : G) ∈ c.Ts := by
    change y ∈ (P : Subgroup c.Gs) at hy
    rwa [hP] at hy
  exact Subtype.ext (hxc y hyT)

/-- All hypotheses of the transfer calculation now follow from the actual
J.2.3 product, its Suzuki two-group and Singer orbit, and J.2.7's Sylow. -/
theorem disjoint_S0_Ls_of_suzuki_two_group [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7) : Disjoint c.S0 c.Ls := by
  obtain ⟨hc, hi⟩ := c.local_product_transfer_geometry P hP e he hsuzuki htrans
  exact c.disjoint_S0_Ls_of_local_product P hP e he
    (c.Ts_derived_eq_V hsuzuki.2.1 htrans) hCL hc hi

/-- The earlier orders of the local product force the Suzuki Sylow order. -/
theorem S1_card_of_local_product
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1) (hS0 : Nat.card c.S0 = 4) (hTs : Nat.card c.Ts = 256) :
    Nat.card c.S1 = 64 := by
  have hPc : Nat.card P = Nat.card c.Ts := by
    calc
      Nat.card P = Nat.card (c.Ts.subgroupOf c.Gs) :=
        congrArg (fun K : Subgroup c.Gs => Nat.card K) hP
      _ = Nat.card c.Ts := Nat.card_congr
        (subgroupOfEquivOfLe (show c.Ts ≤ c.Gs from inf_le_right)).toEquiv
  have hec := Nat.card_congr e.toEquiv
  rw [hPc, hTs, Nat.card_prod, hS0] at hec
  omega

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
