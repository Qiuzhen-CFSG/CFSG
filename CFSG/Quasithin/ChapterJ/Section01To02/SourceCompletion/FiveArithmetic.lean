module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Cubic
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.FiveGroup
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.ModelObstruction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.QuaternionLocal.Quotient

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Quaternion

/-!
# The source order-45 exclusion and five-core conclusion

Only in the hypothetical order-45 case is the odd core conjugated into a
cubic centralizer. Its cubic elements are central by the elementary Sylow
count; a cubic fixed by the chosen z-class inverter then moves into H,
where the genuine source fusion sends it to B. The marked M10 obstruction
excludes this case. The remaining source arithmetic forces order125 and
identifies the odd core with O5(C_G(B5)).

The quaternion witness is constructed from Ru1/Ru2. The separate geometric
inverter construction is the sole premise of `five_core_of_inverter`.

Source: Aschbacher–Smith, J.2.7(5–6), printed pp.435–436.
-/

public section
noncomputable section

open Subgroup
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
private theorem card45_centralizes_cubic {X : Type*} [Group X] [Finite X]
    (hc : Nat.card X = 45) (r : X) (hr : orderOf r = 3) : r ∈ center X := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 3 X := Classical.choice inferInstance
  let Q : Sylow 5 X := Classical.choice inferInstance
  have hP : Nat.card P = 9 := by rw [P.card_eq_multiplicity, hc]; decide +kernel
  have hQ : Nat.card Q = 5 := by rw [Q.card_eq_multiplicity, hc]; decide +kernel
  have hPi : P.index = 5 := by
    have h := (P : Subgroup X).card_mul_index
    rw [hP, hc] at h
    omega
  have hQi : Q.index = 9 := by
    have h := (Q : Subgroup X).card_mul_index
    rw [hQ, hc] at h
    omega
  have hPn : Nat.card (Sylow 3 X) = 1 := by
    have hd := P.card_dvd_index
    rw [hPi] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact h
    · have hm := card_sylow_modEq_one 3 X
      rw [h] at hm
      norm_num [Nat.ModEq] at hm
  have hQn : Nat.card (Sylow 5 X) = 1 := by
    have hd := Q.card_dvd_index
    rw [hQi] at hd
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp
      (show Nat.card (Sylow 5 X) ∣ 3 ^ 2 from hd)
    have hm := card_sylow_modEq_one 5 X
    rw [he] at hm ⊢
    interval_cases k <;> first | rfl | norm_num [Nat.ModEq] at hm
  let : Subsingleton (Sylow 3 X) := (Nat.card_eq_one_iff_unique.mp hPn).1
  let : Subsingleton (Sylow 5 X) := (Nat.card_eq_one_iff_unique.mp hQn).1
  have hPN : (P : Subgroup X).Normal := P.normal_of_subsingleton
  have hQN : (Q : Subgroup X).Normal := Q.normal_of_subsingleton
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP
  have hd : Disjoint (P : Subgroup X) (Q : Subgroup X) :=
    disjoint_of_coprime_natCard (by rw [hP, hQ]; decide)
  have hsup : (P : Subgroup X) ⊔ Q = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (by rw [normalizer_eq_top]; exact le_top) hd, hP, hQ, hc]
  have hrP : r ∈ P := by
    obtain ⟨R, hR⟩ := (IsPGroup.of_card (p := 3) (n := 1)
      (show Nat.card (zpowers r) = 3^1 by rw [Nat.card_zpowers, hr]; rfl)).exists_le_sylow
    have he : R = P := Subsingleton.elim _ _
    exact he ▸ hR (mem_zpowers r)
  have hcent : (P : Subgroup X) ⊔ Q ≤ centralizer ({r} : Set X) := by
    apply sup_le
    · intro x hx
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : P) ⟨r, hrP⟩)
    · intro x hx
      apply mem_centralizer_singleton_iff.mpr
      exact (commute_of_normal_of_disjoint _ _ hPN hQN hd r x hrP hx).eq.symm
  apply mem_center_iff.mpr
  intro x
  exact mem_centralizer_singleton_iff.mp (hcent (hsup ▸ mem_top x))
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Only the hypothetical order-45 odd core embeds in a cubic centralizer.
The conclusion is deliberately restricted to that branch. -/
theorem five_odd_card_ne_45 (B5 : Sylow 5 d.toTypeRuSetup.H)
    (q : FiveQuaternionData B5) (v : FiveInverterData c B5) :
    Nat.card (fiveOddPart B5) ≠ 45 := by
  intro h45
  let A := fiveOddPart B5 ⊓ centralizer ({v.i} : Set G)
  have hA : Nat.card A = 3 := by
    have hc := v.oddPart_card_formula c B5 d.card_Z q
    rw [h45] at hc
    rcases v.fixed_card_cases c B5 d.toTypeRuSetup.odd_subgroup_card with h | h | h
    · rw [h] at hc
      norm_num at hc
    · exact h
    · rw [h] at hc
      norm_num at hc
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA])
  let rP : fiveOddPart B5 := ⟨r, r.property.1⟩
  have hr3 : orderOf (r : G) = 3 := (Subgroup.orderOf_coe r).trans hr
  have hrP : rP ∈ center (fiveOddPart B5) := card45_centralizes_cubic h45 rP
    ((Subgroup.orderOf_coe rP).symm.trans hr3)
  obtain ⟨k, hk⟩ := isConj_iff.mp v.z_class
  let r' := (MulAut.conj k) (r : G)
  have hr'H : r' ∈ d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff, ← hk]
    change (MulAut.conj k) (r : G) * (MulAut.conj k) v.i =
      (MulAut.conj k) v.i * (MulAut.conj k) (r : G)
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp r.property.2]
  obtain ⟨b, hb, hcontrol⟩ := cubic_generator_control c
  obtain ⟨h, hh⟩ := hcontrol r' hr'H (((MulAut.conj k).orderOf_eq (r : G)).trans hr3)
  let g : G := h*k
  have hgr : (MulAut.conj g) (r : G) = b := by
    change ((h : G)*k) * (r : G) * ((h : G)*k)⁻¹ = b
    simpa only [r', MulAut.conj_apply, mul_inv_rev, mul_assoc] using hh
  have himage : (fiveOddPart B5).map (MulAut.conj g).toMonoidHom ≤ c.GB := by
    rintro x ⟨p, hp, rfl⟩
    change (MulAut.conj g) p ∈ centralizer (c.B : Set G)
    rw [hb, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    rw [← hgr, ← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g)
      (congrArg Subtype.val (mem_center_iff.mp hrP (⟨p, hp⟩ : fiveOddPart B5)))
  obtain ⟨e, _⟩ := cubic_quotient c
  apply c.no_subgroup_order45 (B_card c) e _ himage
  rw [card_map_of_injective (MulAut.conj g).injective, h45]

/-- J.2.7(5–6) after constructing the two independent geometric witnesses. -/
theorem five_core (B5 : Sylow 5 d.toTypeRuSetup.H)
    (q : FiveQuaternionData B5) (v : FiveInverterData c B5) :
    G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 ∧
      Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
      Nat.card (pCoreIn 5 (G5 B5)) = 125 ∧ NotConjToLB c B5 := by
  obtain ⟨e, _⟩ := cubic_quotient c
  exact c.five_core_conclusions_of_calculations B5 d.card_Z (B_card c) q v
    d.toTypeRuSetup.odd_subgroup_card (five_odd_card_ne_45 c B5 q v)
    (c.residual_sylow_five_card (B_card c) e)
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The five-centralizer conclusion after the one remaining geometric inverter input.
All quaternion, odd-core and M10 inputs have their genuine source producers. -/
theorem five_core_of_inverter (B5 : Sylow 5 d.toTypeRuSetup.H)
    (v : FiveInverterData c B5) :
    G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 ∧
      Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
      Nat.card (pCoreIn 5 (G5 B5)) = 125 ∧ NotConjToLB c B5 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  exact five_core c B5 q v
end CFSG.Quasithin.ChapterJ.SourceCompletion
