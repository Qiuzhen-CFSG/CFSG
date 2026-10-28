module
public import Theory.Representation.BinaryOffender.FaithfulComponentPair
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Displacement in the centralizer of a Suzuki component

A nonidentity commuting actor has a nonzero displacement submodule. When
Suzuki has no fixed vectors on the ambient space, simplicity makes its
action on that displacement faithful. The minimum binary degree therefore
bounds the displacement by 4(2m+1). For an involution, rank-nullity doubles
this bound on the ambient degree. A ratio-two elementary actor meeting
the centralizer consequently has rank at least 2(2m+1).

No constituent, homogeneity or tensor coordinates are assumed. The literal
Chapter 10 Hall application is SeedAnalysis.SuzukiBounds.
Source: Aschbacher--Smith D.3.9, printed pp.200--201; the Suzuki minimum
degree uses the primitive-prime proof in Suzuki.BinaryDegree.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.Suzuki
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every nonidentity centralizing element has a faithful displacement module. -/
theorem centralizer_displacement_bound
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (S : Subgroup G) (hfix : fixedSpace ρ S = ⊥)
    (m : ℕ) (hm : 0 < m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (a : G) (ha : a ∈ centralizer (S : Set G)) (hne : a ≠ 1) :
    4 * (2*m+1) ≤ fixedCodim ρ (zpowers a) := by
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup S := e.isSimpleGroup
  let U : Subrepresentation (ρ.comp S.subtype) := {
    toSubmodule := LinearMap.range (ρ a - LinearMap.id)
    apply_mem_toSubmodule s v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨ρ s w,?_⟩
      change ρ a (ρ s w) - ρ s w = ρ s (ρ a w - w)
      rw [map_sub]
      congr 1
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
      exact LinearMap.congr_fun (congrArg ρ (ha s s.property).symm) w }
  have hU : U ≠ ⊥ := by
    intro he
    apply hne
    apply hf
    rw [map_one]
    ext v
    have hv : ρ a v - v ∈ U.toSubmodule := ⟨v,rfl⟩
    have hz : U.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [hz,Submodule.mem_bot] at hv
    exact sub_eq_zero.mp hv
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot
    (ρ.comp S.subtype) hfix U hU
  have hd := finrank_ge (by omega : 1 ≤ m)
    (U.toRepresentation.comp e.symm.toMonoidHom) (hfaith.comp e.symm.injective)
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hd

variable [Finite G]
/-- A commuting involution forces at least twice the minimum faithful degree. -/
theorem centralizer_involution_degree_bound
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (S : Subgroup G) (hfix : fixedSpace ρ S = ⊥)
    (m : ℕ) (hm : 0 < m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (a : G) (ha : a ∈ centralizer (S : Set G)) (hne : a ≠ 1) (ha2 : a^2=1) :
    8 * (2*m+1) ≤ Module.finrank (ZMod 2) V := by
  have hlow := centralizer_displacement_bound ρ hf S hfix m hm e a ha hne
  have hord : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha2,hne⟩
  have hu := (involution_actor_rank_and_fixedCodim ρ a hord).2.2.2
  omega

/-- A ratio-two elementary actor with nontrivial component centralizer has
large rank and large ambient degree. -/
theorem small_actor_centralizer_rank_bound
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (S : Subgroup G) (hfix : fixedSpace ρ S = ⊥)
    (m : ℕ) (hm : 0 < m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hb : fixedCodim ρ A ≤ 2*rank A)
    (hne : A ⊓ centralizer (S : Set G) ≠ ⊥) :
    2 * (2*m+1) ≤ rank A ∧ 8 * (2*m+1) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨a,ha,ha1⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ A ⊓ centralizer (S : Set G) ≤ ⊥ from fun h => hne (bot_unique h))
  have hane : a ≠ 1 := fun h => ha1 (mem_bot.mpr h)
  have hd := centralizer_displacement_bound ρ hf S hfix m hm e a ha.2 hane
  have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha.1))
  have hdimA := fixedCodim_add_finrank ρ A
  have hdima := fixedCodim_add_finrank ρ (zpowers a)
  let : IsElementaryAbelian 2 A := hA.2
  exact ⟨by omega,centralizer_involution_degree_bound ρ hf S hfix m hm e a ha.2 hane
    (elemPow_eq_one_of_isElementaryAbelian a ha.1)⟩
end Representation.Suzuki
