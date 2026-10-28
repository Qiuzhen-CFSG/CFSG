module
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# Elementary sections from central displacement

If a group displaces a subgroup into a central elementary two-subgroup,
every square centralizes the actor. The quotient by the full actor centralizer
is therefore elementary, even when the original subgroup is nonabelian.
For a perfect actor, its fixed space on this literal quotient is zero: a
second commutator vanishes and perfectness removes the first commutator.

These are the section arguments used in MS93 (3.4), printed p.869, to retain
the entire fixed layer in the source star quotient.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G J : Type*} [Group G] [Group J]

/-- Squares centralize the actor when displacement is central of exponent two. -/
theorem central_displacement_square (A L U : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hmove : ⁅A,L⁆ ≤ U) (hc : U ≤ centralizer (A : Set G))
    (a : A) : (a : G)^2 ∈ centralizer (L : Set G) := by
  intro l hl
  have hla : ⁅l,(a:G)⁆ ∈ U := hmove (by
    rw [commutator_comm]
    exact commutator_mem_commutator hl a.property)
  have hcomm : Commute ⁅l,(a:G)⁆ (a:G) := (hc hla a a.property).symm
  have hpow : ⁅l,(a:G)⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hla
  have he : l * (a:G) * l⁻¹ = ⁅l,(a:G)⁆ * a := by
    simp [commutatorElement_def,mul_assoc]
  have hsq : l * (a:G)^2 * l⁻¹ = (a:G)^2 := by
    rw [← MulAut.conj_apply,map_pow, MulAut.conj_apply,he,hcomm.mul_pow,hpow,one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hsq

/-- The quotient by the full actor centralizer is elementary. -/
theorem central_displacement_quotient_elementary (A L U : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hmove : ⁅A,L⁆ ≤ U) (hc : U ≤ centralizer (A : Set G))
    [((centralizer (L : Set G)).subgroupOf A).Normal] :
    IsElementaryAbelian 2 (A ⧸ (centralizer (L : Set G)).subgroupOf A) := by
  let N := (centralizer (L : Set G)).subgroupOf A
  have hsquare (v : A ⧸ N) : v^2=1 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N v
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (central_displacement_square A L U hmove hc a)
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquare x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

end Subgroup
namespace Representation.BinaryConjugationSection
variable {G J : Type*} [Group G] [Group J]

/-- A literal section by the full centralizer has no new fixed vectors for a
perfect actor, even if the subgroup above the section is not abelian. -/
theorem fixed_section_eq_bot (S A L : Subgroup G) [Group.IsPerfect L]
    (hLS : L ≤ S) (hAL : A ≤ normalizer (L : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : S →* J) (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection S A (A ⊓ centralizer (L : Set G)) (σ.comp κ)) :
    fixedSpace σ ((L.subgroupOf S).map κ) = ⊥ := by
  have hNC : normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hAN : A ≤ normalizer ((A ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (le_inf A.le_normalizer (hAL.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  let B := commutatorPreimage A L (A ⊓ centralizer (L : Set G))
  have hBC : B ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (commutator_commutatorPreimage_le A L _ hAN).trans inf_le_right
  apply bot_unique
  intro v hv
  obtain ⟨a,ha⟩ := c.onto (Multiplicative.ofAdd v)
  have haB : (a:G) ∈ B := by
    apply (mem_commutatorPreimage_iff A L _ hAN _).mpr
    refine ⟨a.property,?_⟩
    intro l hl
    have hlaS : l ∈ S := hLS hl
    let b : A := ⟨l*a*l⁻¹,(mem_normalizer_iff.mp (c.normalized hlaS) a).mp a.property⟩
    have he : c.coordinates b = c.coordinates a := by
      apply Multiplicative.toAdd.injective
      rw [c.equivariant ⟨l,hlaS⟩ a]
      change σ (κ ⟨l,hlaS⟩) (c.coordinates a).toAdd = (c.coordinates a).toAdd
      rw [ha]
      exact hv ⟨κ ⟨l,hlaS⟩,mem_map_of_mem κ hl⟩
    have hh : (b*a⁻¹ : A) ∈ c.coordinates.ker := by
      change c.coordinates (b*a⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [c.kernel_eq] at hh
    have hcomm : ⁅l,(a:G)⁆ ∈ A ⊓ centralizer (L : Set G) := hh
    rw [←commutatorElement_inv]
    exact inv_mem hcomm
  have hz := (c.coordinates_eq_one_iff a).mpr ⟨a.property,hBC haB⟩
  change v=0
  exact Multiplicative.ofAdd.injective (ha.symm.trans hz)
end Representation.BinaryConjugationSection
