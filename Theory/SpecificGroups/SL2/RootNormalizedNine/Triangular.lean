module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Triangularity from root normalization and cubes

In characteristic two, a subgroup normalized by the full upper root group,
all of whose cubes lie in that root group, is upper triangular when the field
has more than two elements. For a matrix with lower-left entry c, its
commutator with u(t) has lower-left entry -c²t and trace 2 + (ct)². The
lower-left entry of the cube is the original entry times trace² - 1.
Varying t rules out c ≠ 0.

This supplies the matrix step for the Borel placement in Aschbacher–Smith,
`refs/quasithin.pdf`, printed p.1164, proof of 15.4.20. It avoids any assumption
that the two-core projects nontrivially to each simple factor.
-/

open Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.RootNormalizedNine
variable {F : Type*} [Field F]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

private theorem cube_lower_entry (g : SL(2, F)) :
    (g ^ 3).val 1 0 = g.val 1 0 * ((g.val 0 0 + g.val 1 1)^2 - 1) := by
  have hd := g.property
  simp only [det_fin_two] at hd
  simp [pow_succ, mul_apply, Fin.sum_univ_two]
  linear_combination -g.val 1 0 * hd

private theorem commutator_lower_entry (g : SL(2, F)) (t : F) :
    (⁅g, u t⁆).val 1 0 = -(g.val 1 0 ^ 2 * t) := by
  simp [commutatorElement_def, adjugate_fin_two, mul_apply, Fin.sum_univ_two,
    transvection_coe]
  ring

private theorem commutator_trace (g : SL(2, F)) (t : F) :
    (⁅g, u t⁆).val 0 0 + (⁅g, u t⁆).val 1 1 = 2 + (g.val 1 0 * t)^2 := by
  have hd := g.property
  simp only [det_fin_two] at hd
  simp [commutatorElement_def, adjugate_fin_two, mul_apply, Fin.sum_univ_two,
    transvection_coe]
  linear_combination 2 * hd


variable [Finite F] [CharP F 2]

public theorem triangular_of_cube_mem (g : SL(2, F)) (hq : 2 < Nat.card F)
    (hc : ∀ t : F, ⁅g, u t⁆ ^ 3 ∈ upperUnipotent F) : g ∈ rankOneBorel F := by
  apply (mem_rankOneBorel_iff g).mpr
  by_contra hg
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  let t : F := (a : F) / g.val 1 0
  have ht : t ≠ 0 := div_ne_zero a.ne_zero hg
  have hct : g.val 1 0 * t = (a : F) := by
    dsimp [t]
    field_simp
  obtain ⟨b, hb⟩ := (mem_upperUnipotent F _).mp (hc t)
  have hz : (⁅g, u t⁆ ^ 3).val 1 0 = 0 := by
    rw [← hb]
    simp [transvection_coe]
  rw [cube_lower_entry, commutator_lower_entry, commutator_trace, hct] at hz
  have hz' : (2 + (a : F)^2)^2 - 1 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hg) ht))
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have haa : ((a : F)^2)^2 = 1 := by simpa [htwo, sub_eq_zero] using hz'
  have hasq : (a : F)^2 = 1 := (frobenius_inj F 2) (by simpa [frobenius_def] using haa)
  have ha1 : (a : F) = 1 := (frobenius_inj F 2) (by simpa [frobenius_def] using hasq)
  exact ha (Units.ext ha1)

/-- Cubes in the root group force a root-normalized subgroup to be triangular. -/
public theorem le_borel_of_cubes (C : Subgroup (SL(2, F))) (hq : 2 < Nat.card F)
    (hn : upperUnipotent F ≤ Subgroup.normalizer (C : Set _))
    (hc : ∀ g ∈ C, g ^ 3 ∈ upperUnipotent F) : C ≤ rankOneBorel F := by
  intro g hg
  apply triangular_of_cube_mem g hq
  intro t
  apply hc
  have ht := hn ((mem_upperUnipotent F _).mpr ⟨t, rfl⟩)
  simpa only [commutatorElement_def, mul_assoc] using
    C.mul_mem hg ((Subgroup.mem_normalizer_iff.mp ht g⁻¹).mp (C.inv_mem hg))

end Matrix.SpecialLinearGroup.RootNormalizedNine
