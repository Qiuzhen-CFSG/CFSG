module

public import Stellmacher.Recognition.FongWreathedRationalPacket
public import Stellmacher.Recognition.FongWreathedRestrictionCongruences

/-!
# Actual rows of Fong's rational packet

Choose integer values of the three rational irreducibles at XF squared and
F squared. These choices, together with their already constructed degrees
and involution values, define genuine FongCharacterRow values. Support has
order divisible by eight, so evaluation of the signed decomposition gives
the two order-four row equations. Restriction to the actual Sylow subgroup
gives all four congruences once the F-column values are supplied.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization of
U(3,3), J. Algebra 6 (1967), printed pp.72-74. The full-Sylow congruence is
the completion in the repository's fong-degree-calculation-audit.md.
-/

public section
open scoped BigOperators
open Theory.Character
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Stellmacher.Recognition
open FongWreathedIntrinsic FongWreathedInduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Every support element has order divisible by eight. -/
theorem FongWreathedInduction.InducingData.eight_dvd_orderOf_of_support
    (d : InducingData G) (h : d.H) (hh : h ∈ d.support) : 8 ∣ orderOf (h : G) := by
  have hf : (d.f : G) ∈ Subgroup.zpowers ((h : G) ^ Nat.card d.U) := by
    rw [d.support_power_generates_ambient h hh]
    exact Subgroup.mem_zpowers _
  have hn := (orderOf_dvd_of_mem_zpowers hf).trans (orderOf_pow_dvd (x := (h : G)) _)
  simpa only [Subgroup.orderOf_coe, d.order_f] using hn

theorem FongWreathedInduction.actualInducedOne_eq_zero_of_order_four
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (g : G) (hg : orderOf g = 4) : actualInducedOne S P g = 0 := by
  apply (actualInducingData S P).inducedOne_supported
  rintro ⟨h, hh, hc⟩
  have hn := (actualInducingData S P).eight_dvd_orderOf_of_support h hh
  obtain ⟨a, ha⟩ := isConj_iff.mp hc
  have ho := (MulAut.conj a).orderOf_eq (h : G)
  change orderOf (a * (h : G) * a⁻¹) = orderOf (h : G) at ho
  rw [ha, hg] at ho
  rw [← ho] at hn
  norm_num at hn

namespace FongRationalConstituents
variable {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
variable (r : FongRationalConstituents (actualInducedOne S P) ((J P : S) : G))

def row₂ : FongCharacterRow where
  d := r.d₂
  a := r.a₂
  b := (r.integer_values.1 ((X P * F P ^ 2 : S) : G)).choose
  c := (r.integer_values.1 ((F P ^ 2 : S) : G)).choose

def row₃ : FongCharacterRow where
  d := r.d₃
  a := r.a₃
  b := (r.integer_values.2.1 ((X P * F P ^ 2 : S) : G)).choose
  c := (r.integer_values.2.1 ((F P ^ 2 : S) : G)).choose

def row₄ : FongCharacterRow where
  d := r.d₄
  a := r.a₄
  b := (r.integer_values.2.2 ((X P * F P ^ 2 : S) : G)).choose
  c := (r.integer_values.2.2 ((F P ^ 2 : S) : G)).choose

theorem row₂_values :
    r.χ₂ 1 = (r.row₂.d : ℂ) ∧ r.χ₂ (J P : S) = (r.row₂.a : ℂ) ∧
    r.χ₂ (X P * F P ^ 2 : S) = (r.row₂.b : ℂ) ∧
    r.χ₂ (F P ^ 2 : S) = (r.row₂.c : ℂ) :=
  ⟨r.degrees.1, r.involution_values.1,
    (r.integer_values.1 _).choose_spec, (r.integer_values.1 _).choose_spec⟩

theorem row₃_values :
    r.χ₃ 1 = (r.row₃.d : ℂ) ∧ r.χ₃ (J P : S) = (r.row₃.a : ℂ) ∧
    r.χ₃ (X P * F P ^ 2 : S) = (r.row₃.b : ℂ) ∧
    r.χ₃ (F P ^ 2 : S) = (r.row₃.c : ℂ) :=
  ⟨r.degrees.2.1, r.involution_values.2.1,
    (r.integer_values.2.1 _).choose_spec, (r.integer_values.2.1 _).choose_spec⟩

theorem row₄_values :
    r.χ₄ 1 = (r.row₄.d : ℂ) ∧ r.χ₄ (J P : S) = (r.row₄.a : ℂ) ∧
    r.χ₄ (X P * F P ^ 2 : S) = (r.row₄.b : ℂ) ∧
    r.χ₄ (F P ^ 2 : S) = (r.row₄.c : ℂ) :=
  ⟨r.degrees.2.2, r.involution_values.2.2,
    (r.integer_values.2.2 _).choose_spec, (r.integer_values.2.2 _).choose_spec⟩

theorem orderFour_sum : 1 + r.row₂.b - r.row₃.b - r.row₄.b = 0 := by
  have hv := actualInducedOne_eq_zero_of_order_four S P
    ((X P * F P ^ 2 : S) : G) ((Subgroup.orderOf_coe _).trans (XF_sq_orderOf P))
  rw [r.decomposition] at hv
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply] at hv
  rw [r.row₂_values.2.2.1, r.row₃_values.2.2.1, r.row₄_values.2.2.1] at hv
  exact_mod_cast hv

theorem centralFour_sum : 1 + r.row₂.c - r.row₃.c - r.row₄.c = 0 := by
  have hv := actualInducedOne_eq_zero_of_order_four S P
    ((F P ^ 2 : S) : G) ((Subgroup.orderOf_coe _).trans (F_sq_orderOf P))
  rw [r.decomposition] at hv
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply] at hv
  rw [r.row₂_values.2.2.2, r.row₃_values.2.2.2, r.row₄_values.2.2.2] at hv
  exact_mod_cast hv

omit [Finite G] in
private theorem isCharacter_of_irreducible {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : IsCharacter χ := by
  obtain ⟨n, ρ, _, hρ⟩ := hχ
  exact ⟨n, ρ, hρ⟩

theorem restriction_congruences [IsSimpleGroup G] (ho : BaseOrientation S P)
    (hF₂ : r.χ₂ (F P : S) = 1) (hF₃ : r.χ₃ (F P : S) = -1)
    (hF₄ : r.χ₄ (F P : S) = -1) :
    FongRestrictionCongruences r.row₂ 1 ∧ FongRestrictionCongruences r.row₃ (-1) ∧
      FongRestrictionCongruences r.row₄ (-1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fongRestrictionCongruences_of_character S P ho
      (isCharacter_of_irreducible r.irreducible.1) r.integer_values.1 _ _
      r.row₂_values.1 r.row₂_values.2.1 r.row₂_values.2.2.1 r.row₂_values.2.2.2
      (by simpa using hF₂)
  · exact fongRestrictionCongruences_of_character S P ho
      (isCharacter_of_irreducible r.irreducible.2.1) r.integer_values.2.1 _ _
      r.row₃_values.1 r.row₃_values.2.1 r.row₃_values.2.2.1 r.row₃_values.2.2.2
      (by simpa using hF₃)
  · exact fongRestrictionCongruences_of_character S P ho
      (isCharacter_of_irreducible r.irreducible.2.2) r.integer_values.2.2 _ _
      r.row₄_values.1 r.row₄_values.2.1 r.row₄_values.2.2.1 r.row₄_values.2.2.2
      (by simpa using hF₄)

end FongRationalConstituents
end Stellmacher.Recognition
