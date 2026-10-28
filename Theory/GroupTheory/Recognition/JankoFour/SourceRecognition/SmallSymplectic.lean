module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InnerCover
public import Theory.Representation.Mathieu.SmallModules.M22SymplecticExclusion
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging

/-!
# Excluding the simple Mathieu cover without irreducibility

A faithful binary M₂₂ action of degree at most twelve has a nontrivial
irreducible section. James recognition identifies it with the ten-dimensional
Todd module or its dual. The remaining layers have degree at most two and
are trivial, by simplicity and the order-eleven degree bound. An order-seven
subgroup therefore has displacement nine on the whole space. Odd-order
averaging makes its fixed space nondegenerate for any invariant alternating
form; the resulting even displacement contradicts nine.

This removes the reducible simple-cover possibility in Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), (4.1),
printed p.597, DOI 10.1007/BF01232280. The literal core-action application
is in `SourceRecognition.SourceModule`. James recognition and the native
seven-fixed-space calculations are supplied by the imported Mathieu modules.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Representation Representation.BinaryOffender Sporadic.Mathieu
open Module MathieuCode Representation.MathieuSmall
open scoped BigOperators

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Odd-order fixed spaces of a nondegenerate alternating binary action
have even dimension, with no irreducibility assumption. -/
theorem odd_fixed_even (ρ : Representation (ZMod 2) D V)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (A : Subgroup D) [Finite A] (ho : Odd (Nat.card A)) :
    Even (finrank (ZMod 2) (fixedSpace ρ A)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let C := fixedSpace ρ A
  have hl : (B.restrict C).SeparatingLeft := by
    intro v hv
    apply Subtype.ext
    apply hn.1 v.val
    intro w
    let z : V := ∑ a : A, ρ a w
    have hz : z ∈ C := by
      intro a
      change ρ a (∑ b : A, ρ b w) = ∑ b : A, ρ b w
      simp only [map_sum, ← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun b => rfl)
    have hzero : B v.val z = 0 := hv ⟨z,hz⟩
    have hpair (a : A) : B v.val (ρ a w) = B v.val w := by
      simpa only [show ρ a v.val = v.val from v.property a] using hp a v.val w
    have he : B v.val z = B v.val w := by
      change B v.val (∑ a : A, ρ a w) = _
      rw [map_sum]
      simp only [hpair, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      have hc : (Fintype.card A : ZMod 2) = 1 := by
        simpa only [Nat.card_eq_fintype_card] using ho.natCast_zmod_two
      rw [hc, one_smul]
    exact he.symm.trans hzero
  apply AlternatingForm.even_finrank (B.restrict C) (fun v => ha v.val)
  refine ⟨hl, ?_⟩
  intro v hv
  apply hl v
  intro w
  change B v.val w.val = 0
  rw [← ha.neg_eq w.val v.val]
  exact neg_eq_zero.mpr (hv w)

private theorem m22_trivial_of_degree_lt_ten
    (ρ : Representation (ZMod 2) M22 V) (hd : finrank (ZMod 2) V < 10) : ρ = 1 := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  rcases ρ.normal_ker.eq_bot_or_eq_top with hk | hk
  · have hb := BinaryPrimeDegree.orderOf_le_finrank ρ (ρ.ker_eq_bot_iff.mp hk)
      (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
    rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hb
    omega
  · exact MonoidHom.ker_eq_top_iff.mp hk

private theorem fixedCodim_trivial (ρ : Representation (ZMod 2) D V)
    (hρ : ρ = 1) (A : Subgroup D) : fixedCodim ρ A = 0 := by
  apply (fixedCodim_eq_zero_iff ρ A).mpr
  apply top_unique
  intro v _ a
  rw [hρ]
  rfl

private theorem displacement_add_odd (ρ : Representation (ZMod 2) D V)
    (U : Subrepresentation ρ) (A : Subgroup D) [Finite A] (ho : Odd (Nat.card A)) :
    fixedCodim U.quotientRepresentation A + fixedCodim U.toRepresentation A =
      fixedCodim ρ A := by
  have hf := finrank_fixedSpace_quotient_of_odd ρ U A ho
  have ha := fixedCodim_add_finrank U.toRepresentation A
  have hq := fixedCodim_add_finrank U.quotientRepresentation A
  have hv := fixedCodim_add_finrank ρ A
  have hd := U.toSubmodule.finrank_quotient_add_finrank
  omega

private theorem small_m22_seven (ρ : Representation (ZMod 2) M22 V)
    [IsIrreducible ρ] (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V ≤ 12) :
    finrank (ZMod 2) V = 10 ∧
      ∃ A : Subgroup M22, Nat.card A = 7 ∧ fixedCodim ρ A = 9 := by
  obtain ⟨e,hE⟩ := M22Recognition.of_small_degree ρ hf hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,ha7⟩ := exists_prime_orderOf_dvd_card' (G := M22) 7
    (by rw [m22_order]; norm_num)
  let A : Subgroup M22 := zpowers (e.symm a)
  have hc : Nat.card A = 7 :=
    (Nat.card_zpowers (e.symm a)).trans ((e.symm.orderOf_eq a).trans ha7)
  have hmap : A.map e.toMonoidHom = zpowers a := by
    change (zpowers (e.symm a)).map e.toMonoidHom = zpowers a
    simp only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply]
  rcases hE with hE | hE
  all_goals obtain ⟨E⟩ := hE
  · have hdim := E.toLinearEquiv.finrank_eq
    rw [finrank_m22Cocode] at hdim
    have he := fixedSpace_map_equivariant ρ m22CocodeRepresentation e.toMonoidHom
      E.toLinearEquiv (fun g w => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) w) A
    have hh := E.toLinearEquiv.finrank_map_eq (fixedSpace ρ A)
    rw [he,hmap,m22_cocode_fixed_finrank_seven _ ((Nat.card_zpowers a).trans ha7)] at hh
    have hb := fixedCodim_add_finrank ρ A
    exact ⟨hdim, A, hc, by omega⟩
  · have hdim := E.toLinearEquiv.finrank_eq
    rw [finrank_m22Code] at hdim
    have he := fixedSpace_map_equivariant ρ m22CodeRepresentation e.toMonoidHom
      E.toLinearEquiv (fun g w => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) w) A
    have hh := E.toLinearEquiv.finrank_map_eq (fixedSpace ρ A)
    rw [he,hmap,m22_code_fixed_finrank_seven _ ((Nat.card_zpowers a).trans ha7)] at hh
    have hb := fixedCodim_add_finrank ρ A
    exact ⟨hdim, A, hc, by omega⟩

/-- No faithful binary M₂₂ action of degree at most twelve preserves a
nondegenerate alternating form, including reducible actions. -/
theorem m22_not_symplectic_of_degree_le_twelve
    (ρ : Representation (ZMod 2) M22 V) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V ≤ 12)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) : False := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let := m22_perfect
  let : Group.IsPerfect (⊤ : Subgroup M22) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv : (⊤ : Subgroup M22) ≃* M22).symm.toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup M22) ≃* M22).symm.surjective
  have hne : ¬ (⊤ : Subgroup M22) ≤ ρ.ker := by
    intro hh
    have ht : (⊤ : Subgroup M22) = ⊥ := top_unique hh ▸ (ρ.ker_eq_bot_iff.mpr hf)
    exact top_ne_bot ht
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup M22) hne
  let σ := N.quotientRepresentation
  let := hi
  have hs : Function.Injective σ := by
    rcases σ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact σ.ker_eq_bot_iff.mp hb
    · exact (hN ht.ge).elim
  have hU := U.toSubmodule.finrank_le
  have hQ := Submodule.finrank_quotient_le N.toSubmodule
  obtain ⟨hdim,A,hA,hcod⟩ := small_m22_seven σ hs (by omega)
  have hNdim := N.toSubmodule.finrank_quotient_add_finrank
  have hUdim := U.toSubmodule.finrank_quotient_add_finrank
  have htrN := m22_trivial_of_degree_lt_ten N.toRepresentation (by
    change finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) = 10 at hdim
    omega)
  have htrU := m22_trivial_of_degree_lt_ten U.quotientRepresentation (by
    change finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) = 10 at hdim
    omega)
  have ho : Odd (Nat.card A) := hA ▸ (by decide)
  have hsN := displacement_add_odd U.toRepresentation N A ho
  have hsU := displacement_add_odd ρ U A ho
  have hzN := fixedCodim_trivial N.toRepresentation htrN A
  have hzU := fixedCodim_trivial U.quotientRepresentation htrU A
  have hv := fixedCodim_add_finrank ρ A
  obtain ⟨r,hr⟩ := AlternatingForm.even_finrank B ha hn
  obtain ⟨s,hs⟩ := odd_fixed_even ρ B ha hn hp A ho
  change fixedCodim N.quotientRepresentation A = 9 at hcod
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
