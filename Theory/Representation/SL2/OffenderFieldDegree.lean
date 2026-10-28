module
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.Representation.SL2.BinaryInvolutionDisplacement
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.ScalarCoinvariants
public import Theory.SpecificGroups.SL2.SylowConsequences
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Scalar degrees forced by offenders in an embedded SL₂

A nontrivial binary representation of SL₂(2ⁿ) has an irreducible section of
size at least 2n. Every nonidentity involution moves at least half of that
section, hence at least n dimensions of the original representation.
An elementary offender contained in an actual SL₂(2ⁿ) subgroup has rank
at most n by the Sylow order. Its fixed codimension is therefore exactly n.
When the faithful action is defined over a larger binary field, restriction
of scalars shows that this field's degree divides n.

Source: Aschbacher–Smith E.2.13(4), printed p.225, and the action-table
comparison in 4.3.6, p.615. The involution estimate uses the actual
highest-weight calculation in BinaryInvolutionDisplacement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

/-- Every nonidentity involution moves at least the defining field degree. -/
theorem involution_fixedCodim_lower
    (ρ : Representation (ZMod 2) SL(2,K) V) (hnt : ∃ g, ρ g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n)
    (g : SL(2,K)) (hg : g ≠ 1) (hg2 : g^2 = 1) :
    n ≤ fixedCodim ρ (zpowers g) := by
  have hlarge : 3 < Nat.card K := by
    rw [hK]
    have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ n)
    norm_num at this ⊢
    omega
  let : Group.IsPerfect SL(2,K) := GorensteinWalter.sl2_isPerfect_of_card_gt_three K hlarge
  let : Group.IsPerfect (⊤ : Subgroup SL(2,K)) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := SL(2,K))).symm.toMonoidHom) topEquiv.symm.surjective
  have hne : ¬ (⊤ : Subgroup SL(2,K)) ≤ ρ.ker := by
    intro h
    obtain ⟨a,ha⟩ := hnt
    exact ha (h (mem_top a))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup SL(2,K)) hne
  let := hi
  have hntN : ∃ a, N.quotientRepresentation a ≠ 1 := by
    by_contra! he
    exact hN (fun a _ => he a)
  have hd := Unsigned.irreducible_finrank_bound 2 N.quotientRepresentation hntN n (by omega) hK
  have hb := binary_involution_displacement N.quotientRepresentation hntN g hg hg2
  have hdisp := fixedCodim_zpowers_eq_displacement_rank N.quotientRepresentation g
  change fixedCodim N.quotientRepresentation (zpowers g) =
    Module.finrank (ZMod 2) (LinearMap.range (N.quotientRepresentation g - 1)) at hdisp
  rw [←hdisp] at hb
  have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N (zpowers g)
  have hu := fixedCodim_subrepresentation_le ρ U (zpowers g)
  omega

variable {H : Type*} [Group H] [Finite H]
/-- An offender inside the specified rank-one subgroup has exact fixed codimension. -/
theorem offender_fixedCodim_eq_fieldDegree
    (ρ : Representation (ZMod 2) H V) (hf : Function.Injective ρ)
    (J A : Subgroup H) (hAJ : A ≤ J) (e : J ≃* SL(2,K))
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n)
    (hA : IsOffender ρ A) : fixedCodim ρ A = n := by
  let f := J.subtype.comp e.symm.toMonoidHom
  let σ := ρ.comp f
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  let aJ : J := ⟨a,hAJ ha⟩
  have hg : e aJ ≠ 1 := by
    intro he
    exact hane (congrArg Subtype.val (e.injective (he.trans e.map_one.symm)))
  let := hA.1.2
  have hg2 : (e aJ)^2 = 1 := by
    rw [←map_pow]
    apply e.map_eq_one_iff.mpr
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hnt : ∃ g, σ g ≠ 1 := by
    refine ⟨e aJ,?_⟩
    intro he
    have hh : ρ a = 1 := by simpa [σ,f,aJ] using he
    exact hane (hf (hh.trans ρ.map_one.symm))
  have hl := involution_fixedCodim_lower σ hnt hn hK (e aJ) hg hg2
  have hmap : (zpowers (e aJ)).map f = zpowers a := by
    rw [MonoidHom.map_zpowers]
    simp [f,aJ]
  have he : fixedCodim σ (zpowers (e aJ)) = fixedCodim ρ (zpowers a) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,hmap]
  rw [he] at hl
  have hlow := hl.trans (Representation.BinaryOffender.NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha))
  have hp : IsPGroup 2 (A.subgroupOf J) :=
    (IsElementaryAbelian.subgroupOf hAJ).isPGroup
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hsc : Nat.card S = 2^n := by
    let SK := S.mapSurjective (f := e.toMonoidHom) e.surjective
    calc
      Nat.card S = Nat.card SK := Nat.card_congr
        ((S : Subgroup J).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card K := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 SK).symm.toEquiv
      _ = _ := hK
  have hc : Nat.card A ≤ 2^n := by
    rw [←hsc,←Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv]
    exact Nat.card_le_card_of_injective _ (inclusion_injective hS)
  rw [hA.1.card_eq_two_pow_rank] at hc
  have hr := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc
  exact le_antisymm (hA.2.trans hr) hlow

/-- The scalar field degree divides the original rank-one field degree. -/
theorem scalar_degree_dvd_of_offender
    {F W : Type*} [Field F] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module F W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F W] [Module.Finite (ZMod 2) W]
    (ρ : Representation F H W)
    (hf : Function.Injective (restrictScalars (k := ZMod 2) ρ))
    (J A : Subgroup H) (hAJ : A ≤ J) (e : J ≃* SL(2,K))
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n)
    (hA : IsOffender (restrictScalars (k := ZMod 2) ρ) A) :
    Module.finrank (ZMod 2) F ∣ n := by
  have he := offender_fixedCodim_eq_fieldDegree
    (restrictScalars (k := ZMod 2) ρ) hf J A hAJ e hn hK hA
  rw [fixedCodim_restrictScalars] at he
  exact ⟨_,he.symm⟩

end Representation.SL2
