module
public import Theory.GroupTheory.PResidual.ActionKernel
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Representation.FrattiniAction
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryResidualSection
public import Theory.Representation.NormalPKernelDescent
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds

/-!
# Suzuki displacement on a residually moved two-group

A nontrivial binary Suzuki action is faithful when the field order is at
least eight. Every nontrivial two-subgroup contains an involution, and the
individual involution estimate gives displacement at least twice the field
degree. A moving irreducible section removes a normal two-kernel. Passing
through the Frattini quotient returns the resulting fixed-index bound to
an arbitrary finite two-group, without assuming that its action is faithful
or that the two-group is elementary.

Source: DGS, *Groups and Graphs* (1985), 5.7 and the end of 8.4, pp.108,138;
the individual Suzuki estimate is the proved 5.10(b) torus argument.
`DGS85.CommutingNontrivial.RadiusThreeSuzuki` applies the bound to the
literal residual section W/V_beta.
-/

public noncomputable section
namespace Representation.Suzuki
open Subgroup BinaryOffender BinaryFixedPoints BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
open scoped IsMulCommutative

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Any nontrivial two-subgroup moves at least two field degrees in a
nontrivial binary action of a large Suzuki group. -/
theorem two_subgroup_fixedCodim_lower {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup (SuzukiMatrixGroup m)) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    2 * (2*m+1) ≤ fixedCodim ρ A := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · obtain ⟨g,hg⟩ := hnt
      exact (hg (show g ∈ ρ.ker from he.symm ▸ mem_top g)).elim
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hdiv : 2 ∣ Nat.card A := (hA.dvd_orderOf
    (show (⟨a,ha⟩ : A) ≠ 1 from fun he => hane (congrArg Subtype.val he))).trans
      (orderOf_dvd_natCard (⟨a,ha⟩ : A))
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdiv
  have ht' : orderOf (t : SuzukiMatrixGroup m) = 2 := (Subgroup.orderOf_coe t).trans ht
  exact (suzuki_involution_field_degree_lower hm ρ hf t ht').trans
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr t.property))

variable {D M : Type*} [Group D] [Finite D]
  [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

/-- The same displacement bound survives a normal two-kernel; residual
movement supplies a nontrivial irreducible quotient action. -/
theorem extension_fixedCodim_lower {m : ℕ} (hm : 0 < m)
    (π : D →* SuzukiMatrixGroup m) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) D M)
    (hmove : fixedSpace ρ (pResidual 2 D) ≠ ⊤)
    (A : Subgroup D) (hA : IsPGroup 2 (A.map π)) (hne : A.map π ≠ ⊥) :
    2 * (2*m+1) ≤ fixedCodim ρ A := by
  have hnot : ¬ pResidual 2 D ≤ ρ.ker := by
    intro hh
    apply hmove
    apply top_unique
    intro v _ a
    exact DFunLike.congr_fun (hh a.property) v
  obtain ⟨U,N,hi,hmoving⟩ := exists_irreducible_section_surviving_twoPerfect
    (pResidual 2 D) (isPPerfect_pResidual 2) hnot
  let := hi
  obtain ⟨τ,hτ,_⟩ := exists_irreducible_descent_of_pGroup_kernel
    N.quotientRepresentation π hπ hk
  have hτnt : ∃ g, τ g ≠ 1 := by
    by_contra! hh
    apply hmoving
    intro a ha
    rw [MonoidHom.mem_ker,←hτ a,hh]
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective N.toSubmodule.mkQ (Submodule.mkQ_surjective _)
  have hl := two_subgroup_fixedCodim_lower hm τ hτnt (A.map π) hA hne
  have he : τ.comp π = N.quotientRepresentation := MonoidHom.ext hτ
  have hcod : fixedCodim τ (A.map π) = fixedCodim N.quotientRepresentation A := by
    rw [←he,fixedCodim,fixedCodim,fixedSpace_comp_map]
  have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
  have hu := fixedCodim_subrepresentation_le ρ U A
  rw [hcod] at hl
  omega

variable {X : Type*} [Group X] [Finite X]

/-- An escaping two-subgroup has fixed index at least the square of the
Suzuki field order on every residually moved finite two-group. -/
theorem twoGroup_fixedIndex_lower_of_residual_moves {m : ℕ} (hm : 0 < m)
    (π : D →* SuzukiMatrixGroup m) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hp : IsPGroup 2 X) (α : D →* MulAut X)
    (hr : ¬ pResidual 2 D ≤ α.ker)
    (A : Subgroup D) (hA : IsPGroup 2 A) (hne : A.map π ≠ ⊥) :
    let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
    (2^(2*m+1))^2 ≤ (FixedPoints.subgroup A X).index := by
  let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
  let : Fact (IsPGroup 2 X) := ⟨hp⟩
  let Y := X ⧸ frattini X
  let : IsElementaryAbelian 2 Y := isElementaryAbelian_quotient_frattini
  let β := (quotientAut (frattini X)).comp α
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hβ := MonoidHom.residual_not_le_frattini_action_kernel hp α hr
  have hmove : fixedSpace ρ (pResidual 2 D) ≠ ⊤ := by
    intro he
    apply hβ
    intro r hr
    apply MulEquiv.ext
    intro x
    have hx : Additive.ofMul x ∈ fixedSpace ρ (pResidual 2 D) := he ▸ Submodule.mem_top
    exact congrArg Additive.toMul (hx ⟨r,hr⟩)
  have hl := extension_fixedCodim_lower hm π hπ hk ρ hmove A (hA.map π) hne
  let τ := ρ.comp A.subtype
  let := action τ
  let f : X →* Multiplicative (Additive Y) := {
    toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini X) x))
    map_one' := (QuotientGroup.mk' (frattini X)).map_one
    map_mul' := (QuotientGroup.mk' (frattini X)).map_mul }
  have heq (a : A) (x : X) : f (a • x) = a • f x := by
    change QuotientGroup.mk' (frattini X) (α a.val x) =
      quotientAut (frattini X) (α a.val) (QuotientGroup.mk' (frattini X) x)
    rw [quotientAut_apply_mk]
  have hi : fixedIndex τ ≤ (FixedPoints.subgroup A X).index :=
    fixedPoints_index_le_of_surjective_equivariant f
      (QuotientGroup.mk'_surjective (frattini X)) heq
  rw [Representation.FrattiniAction.fixedIndex_eq_two_pow_fixedCodim ρ A] at hi
  rw [←pow_mul,Nat.mul_comm (2*m+1) 2]
  exact (Nat.pow_le_pow_right (by decide) hl).trans hi

end Representation.Suzuki
