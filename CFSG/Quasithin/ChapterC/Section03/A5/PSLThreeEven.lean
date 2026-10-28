module
public import CFSG.Quasithin.ChapterC.Section03.A5.PSLThreeEvenCubic
public import Theory.SpecificGroups.PSL3.RealCubicCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The deleted-five block cannot embed in characteristic-two PSL₃

Every cubic in the original A₅ block is real, and the deleted module has a
nonidentity fixed involution. The intrinsic PSL₃ real-cubic centralizer
calculation excludes precisely this pair. The literal block, conjugation
and original ambient equivalence are retained; no bound on a Sylow subgroup
or additional module alignment is required.
Source: Aschbacher–Smith, terminal step of 2.4.25, printed pp.542–543.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The obstruction holds over every finite field of characteristic two. -/
theorem no_alternatingFive_of_pslThree_even_equiv
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (e : G ≃* PSL(3,F)) (A : Subgroup G) (hA : IsAlternatingBlock A 5) : False := by
  obtain ⟨a,_,ha⟩ := hA.exists_sylow_normalizer_cubic (Sylow.nonempty.some : Sylow 2 A)
  have ha3 : a^3=1 := ha ▸ pow_orderOf_eq_one a
  have hane : (a:G)≠1 := by
    intro h
    have ha1 : a=1 := Subtype.ext h
    have hh : (1:ℕ)=3 := by simpa only [ha1,orderOf_one] using ha
    omega
  have har : IsConj (e a) (e a)⁻¹ := by
    rw [←map_inv]
    exact (e.toMonoidHom.comp A.subtype).map_isConj (hA.cubic_real a ha)
  let U := (blockU A).map A.subtype
  let := hA.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map A.subtype
  have hAU : A ≤ normalizer (U:Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  let b : normalizer (U:Set G) := ⟨a,hAU a.property⟩
  let α := U.normalizerMonoidHom b
  have hb3 : b^3=1 := Subtype.ext (congrArg A.subtype ha3)
  have hα3 : α^3=1 := by
    change (U.normalizerMonoidHom b)^3=1
    rw [←map_pow,hb3,map_one]
  apply hA.no_fixedFree_cubic_in_normalizer a (A.le_normalizer a.property) α hα3
  · intro u hu
    by_contra hune
    have ht : e (u:G)≠1 := by
      intro h
      apply hune
      apply Subtype.ext
      exact e.injective (h.trans e.map_one.symm)
    have ht2 : e (u:G)^2=1 := by
      rw [←map_pow]
      rw [elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,map_one]
    have hac : Commute (e (a:G)) (e (u:G)) := by
      have hh := congrArg U.subtype hu
      change (a:G)*(u:G)*(a:G)⁻¹=(u:G) at hh
      change e (a:G)*e (u:G)=e (u:G)*e (a:G)
      rw [←map_mul,←map_mul,mul_inv_eq_iff_eq_mul.mp hh]
    have h := Matrix.PSL3.EvenInnerCentralizers.RealCubic.eq_one_of_centralizes_involution
      hn hF (e (a:G)) (e (u:G)) (by rw [←map_pow,←Subgroup.coe_pow,ha3,Subgroup.coe_one,map_one])
      har ht ht2 hac
    exact hane (e.injective (h.trans e.map_one.symm))
  · intro u
    rfl

/-- The exact centerless linear-three row of the marked model catalogue. -/
theorem no_alternatingFive_of_pslThree_even
    (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    {n : ℕ} (hn : 1≤n) (hmodel : ClassicalGroup.IsPSL G 3 (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact no_alternatingFive_of_pslThree_even_equiv (by omega) hF e A hA

/-- Apply the row to the original block in its literal containing subgroup. -/
theorem no_pslThree_even_subgroup_containing_alternatingFive
    (A X : Subgroup G) (hA : IsAlternatingBlock A 5) (hAX : A≤X)
    {n : ℕ} (hn : 1≤n) (hmodel : ClassicalGroup.IsPSL X 3 (2^n)) : False := by
  let B := A.subgroupOf X
  let a : B ≃* A := subgroupOfEquivOfLe hAX
  have hB : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv a.symm hA
  exact no_alternatingFive_of_pslThree_even B hB hn hmodel

end CFSG.Quasithin.ChapterC
