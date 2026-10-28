module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The binary representation on the source quotient

The already proved source centralizer identity constructs the faithful
conjugation action of H/O₂(H) on U_H/V₁. Linearization uses the canonical
binary vector space on this same elementary abelian quotient. Restricting
the acting group to a subgroup containing a given offender preserves both
its quadratic action and its exact action ratio.

These are the action and restriction bridges for applying D.2.13 in
P*Uγ*. The source assembly must supply the actual local normality,
elementary abelianness, normalization of V₁, and the centralizer identity
from the standing setup on p.946. No module, kernel or faithful image is
substituted for the named source quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the standing
setup on p.946, D.2.1 on p.178, and the proof of 13.8.13 on pp.950–951.
-/

@[expose] public section

open Subgroup
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [(Z.subgroupOf U).Normal] [IsElementaryAbelian 2 U]

/-- The binary representation on the literal subgroup quotient. -/
noncomputable def linearAction (a : Five.StarAction H U Z) :
    Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U)) where
  toFun g := (CriticalGeometry.binaryLinear (a.action g)).toLinearMap
  map_one' := by
    ext v
    change a.action 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' := by
    intro g k
    ext v
    change a.action (g * k) v.toMul = a.action g (a.action k v.toMul)
    rw [map_mul]
    rfl

/-- Linearization preserves the faithfulness of the actual group action. -/
theorem linearAction_injective (a : Five.StarAction H U Z)
    (ha : Function.Injective a.action) : Function.Injective (linearAction a) := by
  intro x y hxy
  apply ha
  ext v
  exact congrArg (fun f => f (Additive.ofMul v)) hxy

/-- The source centralizer identity constructs a faithful binary representation
on U_H/V₁, with the group action and its conjugation formula retained. -/
theorem exists_faithful_source_representation (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁) :
    ∃ a : Five.StarAction H (Source.UH H V₃) V₁,
      Function.Injective (linearAction a) := by
  obtain ⟨a, ha⟩ := Five.exists_faithful_source_starAction H V₃ V₁ hz hk
  exact ⟨a, linearAction_injective a ha⟩

variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- Restricting actors to a subgroup containing A does not change the ratio. -/
theorem actionRatio_subgroupOf (ρ : Representation (ZMod 2) K W)
    (J A : Subgroup K) (hAJ : A ≤ J) :
    actionRatio (ρ.comp J.subtype) (A.subgroupOf J) = actionRatio ρ A := by
  have hf := fixedSpace_comp_map ρ J.subtype (A.subgroupOf J)
  rw [map_subgroupOf_eq_of_le hAJ] at hf
  have hr : rank (A.subgroupOf J) = rank A := by
    unfold rank
    rw [Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv]
  unfold actionRatio fixedCodim
  rw [hf, hr]

/-- Quadraticity is preserved in this same restriction, with no change of module. -/
theorem quadratic_subgroupOf (ρ : Representation (ZMod 2) K W)
    (J A : Subgroup K) (hA : IsQuadratic ρ A) :
    IsQuadratic (ρ.comp J.subtype) (A.subgroupOf J) := by
  intro a ha b hb v
  exact hA a ha b hb v
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders

end
