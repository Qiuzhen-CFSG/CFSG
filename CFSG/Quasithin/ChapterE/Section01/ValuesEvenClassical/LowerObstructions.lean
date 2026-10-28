module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ProjectiveLinear.EvenInvolution
public import Theory.SpecificGroups.SymplecticFour.DerivedInvolution
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lower obstructions for the classical cases of E.1.14(1)

Projective transvections prove even order for the linear alternatives. A
commutator of symplectic transvections does the same for Sp₄(2^f)', including
Sp₄(2)'. Transport through the given model isomorphism and subgroup inclusion
handles every ambient extension, without assumptions on its outer action.

The four imported family proofs construct the elementary families and proper
weak-closure normalizers obstructing E-generation at f-1. They retain the
literal two-core and solvable-radical quotients of E.1.2. The unitary proof
also supplies even order using the actual Hermitian root subgroup, over the
matrix field of order 2^(2f). Normality handles all ambient automorphisms.

The final four theorems supply exactly the two lower-bound inputs of
`parameter_eq_of_upper_and_predecessor` at L = F*(G). They include f = 1
for PSL₃ and derived Sp₄, and impose f ≥ 2 for PSL₂ and PSU₃. The binary
PSL₄ and PSL₅ witnesses supply the even-order input at value one. The source's
SQTK and G = LT guards are not needed for these lower bounds. Upper generation
and the resulting parameter equalities belong to the independent assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.5--6 and E.1.14(1), printed pp.210--211, 214.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical

private theorem charP_two_of_card_pow {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hcard : Nat.card F = 2 ^ f) : CharP F 2 := by
  let := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : f ≠ 0))

private theorem not_odd_card_of_involution {G : Type*} [Group G]
    (x : G) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) : ¬ Odd (Nat.card G) := by
  have ho : orderOf x = 2 := orderOf_eq_prime hx2 hx
  have hd : 2 ∣ Nat.card G := ho ▸ orderOf_dvd_natCard x
  exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hd)

variable {G : Type*} [Group G]

/-- Any subgroup isomorphic to PSLₙ(2^f), n ≥ 2 and f > 0, forces even order
in the ambient group. In particular this applies to its generalized Fitting subgroup. -/
theorem not_odd_card_of_isPSL (L : Subgroup G) {n f : ℕ}
    (hn : 2 ≤ n) (hf : 0 < f) (hmodel : ClassicalGroup.IsPSL L n (2 ^ f)) :
    ¬ Odd (Nat.card G) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hmodel
  let := charP_two_of_card_pow hf hcard
  obtain ⟨x, hx, hx2⟩ :=
    Matrix.ProjectiveSpecialLinearGroup.exists_involution_of_char_two (F := F) hn
  let j := L.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := L.subtype_injective.comp e.symm.injective
  apply not_odd_card_of_involution (j x)
  · exact fun h => hx (hj (h.trans j.map_one.symm))
  · rw [← map_pow, hx2, map_one]

/-- Even order in the PSL₂ alternative, with the source simplicity restriction. -/
theorem not_odd_card_of_isPSL2 (L : Subgroup G) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL L 2 (2 ^ f)) : ¬ Odd (Nat.card G) :=
  not_odd_card_of_isPSL L (by decide) (by omega) hmodel

/-- Even order in the PSL₃ alternative, including PSL₃(2). -/
theorem not_odd_card_of_isPSL3 (L : Subgroup G) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ f)) : ¬ Odd (Nat.card G) :=
  not_odd_card_of_isPSL L (by decide) hf hmodel

/-- The binary dimension-four alternative has even order. -/
theorem not_odd_card_of_isPSL4_two (L : Subgroup G)
    (hmodel : ClassicalGroup.IsPSL L 4 2) : ¬ Odd (Nat.card G) :=
  not_odd_card_of_isPSL L (n := 4) (f := 1) (by decide) (by decide) (by simpa using hmodel)

/-- The binary dimension-five alternative has even order. -/
theorem not_odd_card_of_isPSL5_two (L : Subgroup G)
    (hmodel : ClassicalGroup.IsPSL L 5 2) : ¬ Odd (Nat.card G) :=
  not_odd_card_of_isPSL L (n := 5) (f := 1) (by decide) (by decide) (by simpa using hmodel)

/-- Even order from the actual derived symplectic model, with no perfectness
assumption. The case f = 1 uses Sp₄(2)', not Sp₄(2). -/
theorem not_odd_card_of_derivedSp4 (L : Subgroup G)
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hcard : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) : ¬ Odd (Nat.card G) := by
  let := charP_two_of_card_pow hf hcard
  obtain ⟨x, hx, hx2⟩ := Theory.SpecificGroups.SymplecticFour.exists_involution_derived_of_char_two (F := F)
  let j := L.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := L.subtype_injective.comp e.symm.injective
  apply not_odd_card_of_involution (j x)
  · exact fun h => hx (hj (h.trans j.map_one.symm))
  · rw [← map_pow, hx2, map_one]

section Assembly

open Theory.GroupTheory
variable [Finite G] [IsSimpleGroup (generalizedFitting G)]

/-- Both lower-bound inputs for the PSL₂ clause of E.1.14(1), with no
additional local-structure or ambient-action premise. -/
theorem lower_bounds_of_isPSL2 {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (generalizedFitting G) 2 (2 ^ f)) :
    ¬ Odd (Nat.card G) ∧ (1 < f → ¬ IsEGenerated (f - 1) G) :=
  ⟨not_odd_card_of_isPSL2 (generalizedFitting G) hf hmodel,
    fun _ => not_isEGenerated_of_isPSL2 hf hmodel⟩

/-- Both lower-bound inputs for PSU₃, preserving the arbitrary nondegenerate
Hermitian form and the matrix-field order (2^f)² in the concrete predicate. -/
theorem lower_bounds_of_isPSU3 (T : Sylow 2 G) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 (2 ^ f)) :
    ¬ Odd (Nat.card G) ∧ (1 < f → ¬ IsEGenerated (f - 1) G) :=
  ⟨not_odd_card_of_isPSU3 (generalizedFitting G) (by omega) hmodel,
    fun _ => not_isEGenerated_of_isPSU3 T hf hmodel⟩

omit [IsSimpleGroup (generalizedFitting G)] in
/-- Both lower-bound inputs for PSL₃, including even order at f = 1.
The intrinsic plane argument also covers ambient graph automorphisms. -/
theorem lower_bounds_of_isPSL3 {f : ℕ} (hf : 1 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (generalizedFitting G) 3 (2 ^ f)) :
    ¬ Odd (Nat.card G) ∧ (1 < f → ¬ IsEGenerated (f - 1) G) :=
  ⟨not_odd_card_of_isPSL3 (generalizedFitting G) hf hmodel,
    fun hf' => not_isEGenerated_of_isPSL3 hf' hmodel⟩

/-- Both lower-bound inputs for the actual derived Sp₄ model. At f = 1
the involution lies in Sp₄(2)' itself; at larger f the proved matrix rank
gap supplies the ambient E-generation obstruction. -/
theorem lower_bounds_of_derivedSp4 (T : Sylow 2 G)
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hcard : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) :
    ¬ Odd (Nat.card G) ∧ (1 < f → ¬ IsEGenerated (f - 1) G) :=
  ⟨not_odd_card_of_derivedSp4 (generalizedFitting G) hf hcard e,
    fun hf' => Sp4Lower.not_isEGenerated_of_generalizedFitting T hf' hcard e⟩

end Assembly

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
