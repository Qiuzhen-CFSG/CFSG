module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics
public import Theory.SpecificGroups.G2Even.ParabolicCharacters

/-!
# Full G₂ parabolics cannot have the marked A₅ two-residual

Every solvable quotient of the actual perfect A₅-by-two residual extension
is a two-group. Each full root parabolic surjects onto the field units,
which have nontrivial odd order when the binary field has size at least four.
The original fixed-component application is C27Geometry.G2Exclusion.
Source: Aschbacher--Smith C.2.7, pp.145--147, and 14.7.68(2), pp.1071--1072.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple
open Subgroup Atlas.G2.LieParabolicSetup

theorem g2_parabolic_impossible
    {M k : Type*} [Group M] [Finite M] [Field k] [Finite k] [CharP k 2]
    (h : HasA5TwoResidual M) (hk : 4 ≤ Nat.card k)
    (he : Nonempty (M ≃* (parabolic₁ (F := k))) ∨
      Nonempty (M ≃* (parabolic₂ (F := k)))) : False := by
  have no_units (hu : IsPGroup 2 kˣ) : False := by
    obtain ⟨n,hn,hn'⟩ := field_card (F := k)
    obtain ⟨a,ha⟩ := hu.exists_card_eq
    have he := Nat.card_eq_card_units_add_one k
    rw [ha,hn'] at he
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    cases a with
    | zero => simp only [pow_zero] at he; omega
    | succ a => simp only [hm,pow_succ] at he; omega
  rcases he with hshort | hlong
  · obtain ⟨e⟩ := hshort
    apply no_units
    apply hasA5TwoResidual_solvable_image h
      ((Atlas.G2.ParabolicCharacters.shortScalar (F := k)).comp e.toMonoidHom)
    exact Atlas.G2.ParabolicCharacters.shortScalar_surjective.comp e.surjective
  · obtain ⟨e⟩ := hlong
    apply no_units
    apply hasA5TwoResidual_solvable_image h
      (Atlas.G2.lineScalarHom.comp
        (e.trans (MulEquiv.subgroupCongr Atlas.G2.parabolic_eq_pointStabilizer)).toMonoidHom)
    exact Atlas.G2.lineScalarHom_surjective.comp
      (e.trans (MulEquiv.subgroupCongr Atlas.G2.parabolic_eq_pointStabilizer)).surjective
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple
