module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureSixteenIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenIntersectionNonseed
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionTransfer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCentralFour

/-!
# Actual point transvections on the original pure elementary sixteen

At every nonidentity point x, the original point core has a central
cyclic-four generator c with c²=x. Its conjugation fixes the literal
point-core intersection with the sixteen. Self-centralization excludes
any larger fixed subgroup, and inversion of c by each exterior point
gives the exact action y ↦ x*y. All actors remain in the original group
and in their original point cores.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every point of the actual pure sixteen has an original point-core
element inducing the transvection with its literal point-core fixed eight. -/
theorem TypeAt.sixteen_point_transvection (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8)
    (x : G) (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ c : G, orderOf c = 4 ∧ c ^ 2 = x ∧
      c ∈ (involutionCentralizer x).pCoreIn 2 ∧ c ∈ normalizer (A : Set G) ∧
      A ⊓ involutionCentralizer c = A ⊓ (involutionCentralizer x).pCoreIn 2 ∧
      (∀ y ∈ A ⊓ (involutionCentralizer x).pCoreIn 2, c * y * c⁻¹ = y) ∧
      (∀ y ∈ A, y ∉ (involutionCentralizer x).pCoreIn 2 → c * y * c⁻¹ = x * y) := by
  obtain ⟨W, hxT⟩ := h.exists_typeAt_of_isConj x (hpure x hx hx1)
  let Q := (involutionCentralizer x).pCoreIn 2
  have hxx : x ∈ Q := by
    change x ∈ (pCore 2 (involutionCentralizer x)).map (involutionCentralizer x).subtype
    rw [← hxT.centralizer_fitting]
    exact hxT.seed_le_core hxT.involution_mem_seed
  have hEE : IsElementaryAbelian 2 (A ⊓ Q : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show A ⊓ Q ≤ A from inf_le_left))
      (inclusion_injective _)
  let E : pointCoreEights x := ⟨A ⊓ Q, inf_le_right, ⟨hx, hxx⟩, hEE, hpoints x hx hx1⟩
  have hEn := hxT.eight_in_sixteen_not_seed E A hA inf_le_left
  have hQN := (hxT.nonseed_eight_extension_structure E hEn A inf_le_left inferInstance hA).1
  obtain ⟨c, hc4, hc2, hcZ, _⟩ := hxT.exists_point_core_central_four
  obtain ⟨cQ, hcQ, hec⟩ := hcZ
  have hc : c ∈ Q := hec ▸ cQ.property
  have hcomm (q : G) (hq : q ∈ Q) : Commute q c := by
    rw [← hec]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨q, hq⟩)
  have hcA : c ∉ A := by
    intro hcA
    have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcA)
    rw [hc4] at hd
    norm_num at hd
  have hfixed : A ⊓ involutionCentralizer c = E.val := by
    have hle : E.val ≤ A ⊓ involutionCentralizer c := fun q hq =>
      ⟨hq.1, mem_centralizer_singleton_iff.mpr (hcomm q hq.2).eq⟩
    have hne : A ⊓ involutionCentralizer c ≠ A := by
      intro he
      apply hcA
      rw [← hCA]
      intro a ha
      have haD : a ∈ A ⊓ involutionCentralizer c := by rw [he]; exact ha
      exact mem_centralizer_singleton_iff.mp haD.2
    have hbound : Nat.card (A ⊓ involutionCentralizer c : Subgroup G) ≤ 8 := by
      let D := A ⊓ involutionCentralizer c
      change Nat.card D ≤ 8
      have hh := (D.subgroupOf A).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe (show D ≤ A from inf_le_left)).toEquiv, hA] at hh
      change Nat.card D * D.relIndex A = 16 at hh
      have hi : D.relIndex A ≠ 1 := fun hi => hne
        (le_antisymm inf_le_left (relIndex_eq_one.mp hi))
      have hip : D.relIndex A ≠ 0 := index_ne_zero_of_finite
      have hi2 : 2 ≤ D.relIndex A := by omega
      have hb := Nat.mul_le_mul_left (Nat.card D) hi2
      rw [hh] at hb
      omega
    exact (eq_of_le_of_card_ge hle (hbound.trans_eq E.property.2.2.2.symm)).symm
  refine ⟨c, hc4, hc2, hc, hQN hc, hfixed, ?_, ?_⟩
  · intro y hy
    rw [(hcomm y hy.2).eq.symm, mul_inv_cancel_right]
  · intro y hy hyQ
    have hyH : y ∈ involutionCentralizer x := mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm hy hx)
    have hnc : ¬ Commute y c := by
      intro hh
      have hyE : y ∈ E.val := hfixed ▸
        (show y ∈ A ⊓ involutionCentralizer c from ⟨hy, mem_centralizer_singleton_iff.mpr hh.eq⟩)
      exact hyQ hyE.2
    have hinv := hxT.point_core_central_four_inverted c hc4 ⟨cQ, hcQ, hec⟩ y hyH hnc
    have hinv' : y * c⁻¹ * y⁻¹ = c := by
      have hh := congrArg Inv.inv hinv
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh
    have hmove : y * c⁻¹ = c * y := mul_inv_eq_iff_eq_mul.mp hinv'
    calc
      c * y * c⁻¹ = c * (y * c⁻¹) := mul_assoc _ _ _
      _ = c * (c * y) := by rw [hmove]
      _ = x * y := by rw [← mul_assoc, ← pow_two, hc2]

/-- Original HS data construct a pure self-centralizing elementary sixteen
with a genuine point-core transvection at each of its fifteen points. -/
theorem TypeAt.exists_sixteen_point_transvections (h : TypeAt z V) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      centralizer (A : Set G) = A ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 →
        Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ A, x ≠ 1 → ∃ c : G, orderOf c = 4 ∧ c ^ 2 = x ∧
        c ∈ (involutionCentralizer x).pCoreIn 2 ∧ c ∈ normalizer (A : Set G) ∧
        A ⊓ involutionCentralizer c = A ⊓ (involutionCentralizer x).pCoreIn 2 ∧
        (∀ y ∈ A ⊓ (involutionCentralizer x).pCoreIn 2, c * y * c⁻¹ = y) ∧
        (∀ y ∈ A, y ∉ (involutionCentralizer x).pCoreIn 2 → c * y * c⁻¹ = x * y)) := by
  obtain ⟨u, c, b, E, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hAe, hA16, _, _, _, _, _, hCA, _, _, _, _, hpure, _, hpoints, _⟩ :=
    h.exists_all_point_core_eights
  let A := E.val ⊔ zpowers b
  let : IsElementaryAbelian 2 A := hAe
  exact ⟨A, hAe, hA16, hCA, hpure, hpoints,
    fun x hx hx1 => h.sixteen_point_transvection A hA16 hCA hpure hpoints x hx hx1⟩

end CFSG.Quasithin.HigmanSims
