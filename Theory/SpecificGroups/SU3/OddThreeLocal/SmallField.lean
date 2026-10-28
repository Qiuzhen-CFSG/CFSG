module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Option
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# The permuting-subgroup exclusion in PSU₃(3)

The actual projective matrix group acts on 28 isotropic points. A root
Sylow three-subgroup of order 27 fixes one point and acts freely elsewhere.
Every subgroup U of order nine or 27 can be conjugated into this root group.
If U lies in H with |H| = 32|U|, the H-orbit of the fixed point has size
congruent to one modulo |U|, divides |H|, and is at most 28. These arithmetic
conditions force that orbit to be a singleton. But then H lies in the point
stabilizer of order 216, a contradiction.

A permuting product of U and a Sylow two-subgroup has exactly the forbidden
order. The argument uses only the checked matrix action and transports to
arbitrary Hermitian forms by actual projective equivalences. It needs no
simplicity or multiplier hypothesis.

Source: Huppert, Endliche Gruppen I, II.10.12; Aschbacher–Smith, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section

open Subgroup MulAction
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal

private theorem free_complement_orbit_dvd
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (H U : Subgroup G) (hUH : U ≤ H) (a : X)
    (hfix : ∀ u : U, (u : G) • a = a)
    (hfree : ∀ (u : U) (x : X), x ≠ a → (u : G) • x = x → u = 1) :
    Nat.card U ∣ Nat.card (orbit H a) - 1 := by
  classical
  let : MulAction U (orbit H a) := MulAction.compHom _ (inclusion hUH)
  let a' : orbit H a := ⟨a, mem_orbit_self a⟩
  have hfix' (u : U) : u • a' = a' := Subtype.ext (hfix u)
  let X₀ : SubMulAction U (orbit H a) := {
    carrier := {x | x ≠ a'}
    smul_mem' := by
      intro u x hx he
      apply hx
      apply (MulAction.injective u)
      exact he.trans (hfix' u).symm }
  have hstab (x : X₀) : stabilizer U x = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro u hu
    apply hfree u x.val.val
    · intro he
      exact x.property (Subtype.ext he)
    · exact congrArg (fun y : X₀ => y.val.val) (mem_stabilizer_iff.mp hu)
  have hd : Nat.card U ∣ Nat.card X₀ := by
    let := Fintype.ofFinite (Quotient (orbitRel U X₀))
    rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer U X₀), Nat.card_sigma]
    apply Finset.dvd_sum
    intro ω _
    change Nat.card U ∣ (stabilizer U ω.out).index
    rw [hstab, index_bot]
  have hc := Nat.card_congr (Equiv.optionSubtypeNe a')
  let := Fintype.ofFinite (orbit H a)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hc
  simp only [← Nat.card_eq_fintype_card] at hc
  change Nat.card X₀ + 1 = Nat.card (orbit H a) at hc
  rwa [← hc, Nat.add_sub_cancel]

private theorem small_orbit_exclusion {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 28) (H U : Subgroup G) (hH : Nat.card H = 32 * Nat.card U)
    (hU : Nat.card U = 9 ∨ Nat.card U = 27) (hUH : U ≤ H) (a : X)
    (hfix : ∀ u : U, (u : G) • a = a)
    (hfree : ∀ (u : U) (x : X), x ≠ a → (u : G) • x = x → u = 1)
    (hstab : Nat.card (stabilizer G a) = 216) : False := by
  have hd := free_complement_orbit_dvd H U hUH a hfix hfree
  have hb : Nat.card (orbit H a) ≤ 28 := hX ▸
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hi : Nat.card (orbit H a) ∣ 32 * Nat.card U := by
    simpa only [index_stabilizer, ← Nat.card_coe_set_eq,
      hH] using (stabilizer H a).index_dvd_card
  have hp : 0 < Nat.card (orbit H a) := by
    let : Nonempty (orbit H a) := ⟨⟨a, mem_orbit_self a⟩⟩
    exact Nat.card_pos
  have hc : Nat.card (orbit H a) = 1 := by
    rcases hU with hU | hU <;> rw [hU] at hd hi
    all_goals
      have hn : Nat.card (orbit H a) = 1 ∨ Nat.card (orbit H a) = 10 ∨
          Nat.card (orbit H a) = 19 ∨ Nat.card (orbit H a) = 28 := by omega
      rcases hn with hn | hn | hn | hn
      · exact hn
      all_goals norm_num [hn] at hi
  have hle : H ≤ stabilizer G a := by
    intro g hg
    apply mem_stabilizer_iff.mpr
    have : Subsingleton (orbit H a) := (Nat.card_eq_one_iff_unique.mp hc).1
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨g • a, mem_orbit a (⟨g, hg⟩ : H)⟩ : orbit H a) ⟨a, mem_orbit_self a⟩)
  have hh := card_dvd_of_le hle
  rw [hH, hstab] at hh
  rcases hU with hU | hU <;> norm_num [hU] at hh

private theorem root_action_exclusion
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hG : Nat.card G = 6048) (hX : Nat.card X = 28)
    (V : Subgroup G) (hV : Nat.card V = 27) (a : X)
    (hVfix : ∀ v : V, (v : G) • a = a)
    (hVfree : ∀ (v : V) (x : X), x ≠ a → (v : G) • x = x → v = 1)
    (hstab : Nat.card (stabilizer G a) = 216)
    (H U : Subgroup G) (hH : Nat.card H = 32 * Nat.card U)
    (hU : Nat.card U = 9 ∨ Nat.card U = 27) (hUH : U ≤ H) : False := by
  have hVp : IsPGroup 3 V := IsPGroup.of_card (n := 3) hV
  have hVi : V.index = 224 := by
    have hh := V.card_mul_index
    rw [hV, hG] at hh
    omega
  let P : Sylow 3 G := hVp.toSylow (by rw [hVi]; decide)
  have hUp : IsPGroup 3 U := by
    rcases hU with hU | hU
    · exact IsPGroup.of_card (n := 2) hU
    · exact IsPGroup.of_card (n := 3) hU
  obtain ⟨T, hUT⟩ := hUp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T P
  let e := MulAut.conj g
  let H' := H.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  have hUV : U' ≤ V := by
    have he : (T : Subgroup G).map e.toMonoidHom = V := congrArg Sylow.toSubgroup hg
    exact he ▸ Subgroup.map_mono hUT
  have hcH : Nat.card H' = Nat.card H :=
    card_map_of_injective (f := e.toMonoidHom) e.injective
  have hcU : Nat.card U' = Nat.card U :=
    card_map_of_injective (f := e.toMonoidHom) e.injective
  have hH' : Nat.card H' = 32 * Nat.card U' := by rwa [hcH, hcU]
  have hU' : Nat.card U' = 9 ∨ Nat.card U' = 27 := by rwa [hcU]
  apply small_orbit_exclusion hX H' U' hH' hU' (Subgroup.map_mono hUH) a
  · intro u
    exact hVfix ⟨u, hUV u.property⟩
  · intro u x hx hux
    have he := hVfree ⟨u, hUV u.property⟩ x hx hux
    exact Subtype.ext (congrArg (fun v : V => (v : G)) he)
  · exact hstab

open BenderSuzuki.MatrixGroups BenderSuzuki.External

/-- A three-subgroup cannot have a local overgroup with index 32 in standard PSU₃(3). -/
theorem standard_overgroup_exclusion {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = 9)
    (hfixed : Nat.card {x : E // J.conj x = x} = 3)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (H U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hH : Nat.card H = 32 * Nat.card U)
    (hU : Nat.card U = 9 ∨ Nat.card U = 27) (hUH : U ≤ H) : False := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨hX, ρ, a, _, _, hB, ht, _, hG, _⟩ := huppert_II_10_12 J 3 hcard hfixed hJ
  obtain ⟨V, _, hVB, _, _, _, _, _, hV, _, _, _, hreg, _⟩ := ht
  let X := {x : Projectivization E (Fin 3 → E) // x ∈
    {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0), x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let : Finite X := Nat.finite_of_card_ne_zero (by change Nat.card X = 28 at hX; omega)
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) X := MulAction.compHom X ρ
  apply root_action_exclusion (X := X) hG
    hX V hV a
    (fun v => hVB v.property) ?_ hB H U hH hU hUH
  intro v x hx hfix
  obtain ⟨w, hw, hu⟩ := hreg x x hx hx
  exact (hu v hfix).trans (hu 1 (by simp)).symm

open scoped Pointwise

/-- The degree-28 action excludes both possible permuting products in the standard form. -/
theorem standard_not_permuting {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = 9)
    (hfixed : Nat.card {x : E // J.conj x = x} = 3)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : Nat.card U = 9 ∨ Nat.card U = 27) :
    (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≠ (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro hp
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨_, _, _, _, _, _, _, _, hG, _⟩ := huppert_II_10_12 J 3 hcard hfixed hJ
  have hG' : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 6048 := hG
  have hS : Nat.card S = 32 := by
    rw [S.card_eq_multiplicity, hG']
    decide +kernel
  have hd : Disjoint U (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := disjoint_of_coprime_natCard (by
    rcases hU with hU | hU <;> rw [hU, hS] <;> norm_num)
  have hh := card_set_mul_mul_card_inf U (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  rw [disjoint_iff.mp hd, card_bot, mul_one, hS] at hh
  have hH : Nat.card (U ⊔ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Subgroup _) = 32 * Nat.card U := by
    change Nat.card (↑(U ⊔ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [coe_sup_of_set_mul_comm U S hp]
    simpa only [mul_comm] using hh
  exact standard_overgroup_exclusion J hcard hfixed hJ _ U hH hU le_sup_left

open HermitianForm.OddPrimeSylow.NormalizedOuter

/-- The subgroup exclusion for any Gram matrix over the field of order nine. -/
theorem not_permuting_three_three {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = 9)
    (hconj : ∀ x, J.conj x = x ^ 3)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : Nat.card U = 9 ∨ Nat.card U = 27) :
    (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≠ (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro hp
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hfixed : Nat.card {x : E // J.conj x = x} = 3 := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 3 1 (by decide) hcard hconj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 3 hcard hfixed
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let U' := U.map e.toMonoidHom
  have hc : Nat.card U' = Nat.card U := card_map_of_injective (f := e.toMonoidHom) e.injective
  apply standard_not_permuting (FormTransport.standardForm J) hcard hfixed rfl S' U'
    (by rwa [hc])
  have hh := congrArg (Set.image e) hp
  change (U.map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) * ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) =
    ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) * (U.map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)))
  simpa only [Set.image_mul, Subgroup.coe_map, Sylow.coe_coe, MulEquiv.coe_toMonoidHom] using hh

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal
