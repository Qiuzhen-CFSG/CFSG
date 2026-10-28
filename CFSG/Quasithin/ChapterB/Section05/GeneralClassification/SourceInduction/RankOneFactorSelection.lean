module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.LinearAlgebra.RankOneInvariantPair
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# The original rank-one element belongs to one B.5.6 factor

The action on the literal quotient by global fixed vectors still has rank at
most one. On the direct sum of the two prescribed quotient-image subspaces it
therefore fixes one summand pointwise. That summand's faithful factor action
makes its normal action kernel disjoint from the corresponding factor. In the
actual center-free internal product this kernel lies in the opposite factor.
Thus the same original element belongs to one of the two literal factors.
No cross-action or chosen factor-permutation premise is used.
Source: Aschbacher–Smith, G.6.4, pp.345–346, using B.5.6(3), p.105.
-/

public section

namespace CFSG.Quasithin.ChapterB.SourceInduction
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

theorem SourceTwoFactorCase.rank_one_mem_factor (d : SourceTwoFactorCase ρ) (t : D)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    t ∈ d.first ∨ t ∈ d.second := by
  let σ := (fixed ρ).quotientRepresentation
  let U := (fixed ρ).quotientImage d.firstSpace
  let W := (fixed ρ).quotientImage d.secondSpace
  let δ := σ t - LinearMap.id
  have hδ : Module.finrank (ZMod 2) (LinearMap.range δ) ≤ 1 := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ (fixed ρ) (zpowers t)
    simp only [fixedCodim_zpowers_eq_displacement_rank] at hh
    exact (Nat.le_add_right _ _).trans hh |>.trans hr
  have hinv (X : Subrepresentation σ) : X.toSubmodule.map δ ≤ X.toSubmodule := by
    rintro _ ⟨x,hx,rfl⟩
    exact X.toSubmodule.sub_mem (X.apply_mem_toSubmodule t hx) hx
  have hk (X : Subrepresentation σ) (hx : X.toSubmodule ≤ LinearMap.ker δ) :
      t ∈ X.toRepresentation.ker := by
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact sub_eq_zero.mp (hx x.property)
  have hdis (A : Subgroup D) (X : Subrepresentation σ)
      (hf : Function.Injective (X.toRepresentation.comp A.subtype)) :
      Disjoint X.toRepresentation.ker A := by
    apply Subgroup.disjoint_def.mpr
    intro x hx ha
    have he : (⟨x,ha⟩ : A) = 1 := hf (by
      change X.toRepresentation x = X.toRepresentation 1
      rw [map_one]
      exact hx)
    exact congrArg Subtype.val he
  rcases LinearMap.invariant_disjoint_pair_rank_one δ hδ U.toSubmodule W.toSubmodule
    d.decomposition.disjoint (hinv U) (hinv W) with hu | hw
  · right
    exact d.product.normal_disjoint_first_le_second d.firstCase.center_eq_bot
      U.toRepresentation.ker (hdis _ U d.firstCase.faithful) (hk U hu)
  · left
    let p := d.product.swap
    exact p.normal_disjoint_first_le_second d.secondCase.center_eq_bot
      W.toRepresentation.ker (hdis _ W d.secondCase.faithful) (hk W hw)
end CFSG.Quasithin.ChapterB.SourceInduction
