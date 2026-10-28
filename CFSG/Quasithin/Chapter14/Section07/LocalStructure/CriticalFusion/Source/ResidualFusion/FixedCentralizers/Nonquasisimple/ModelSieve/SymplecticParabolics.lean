module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics
public import Theory.SpecificGroups.SymplecticFour.ParabolicCharacters

/-!
# Excluding full symplectic parabolics with an A₅ two-residual

Every solvable quotient of a group with the actual perfect A₅-by-two
residual is a two-group. A full point or plane parabolic of Sp₄(k)
surjects onto kˣ. In characteristic two and for |k| ≥ 4, its odd order
is greater than one. Thus neither full parabolic can be this stabilizer.

The original fixed-centralizer application is in C27Geometry.SymplecticExclusion.
Source: Aschbacher--Smith, C.2.7(3)(e) and 14.7.68(2), pp.145--147,1071--1072.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple

theorem symplectic_parabolic_impossible
    {M k : Type*} [Group M] [Finite M] [Field k] [Finite k] [CharP k 2]
    (h : HasA5TwoResidual M) (hk : 4 ≤ Nat.card k)
    (he : Nonempty (M ≃* (pointParabolic (F := k))) ∨
      Nonempty (M ≃* (planeParabolic (F := k)))) : False := by
  have no_units (hu : IsPGroup 2 kˣ) : False := by
    let : Fintype k := Fintype.ofFinite k
    obtain ⟨n, _, hn⟩ := FiniteField.card k 2
    have hn' : Nat.card k = 2 ^ (n : ℕ) := by
      simpa only [Nat.card_eq_fintype_card] using hn
    have hnpos : 0 < (n : ℕ) := by
      by_contra hz
      have hz' : (n : ℕ) = 0 := by omega
      simp only [hz', pow_zero] at hn'
      omega
    obtain ⟨a, ha⟩ := hu.exists_card_eq
    have he := Nat.card_eq_card_units_add_one k
    rw [ha, hn'] at he
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    cases a with
    | zero => simp only [pow_zero] at he; omega
    | succ a => simp only [hm, pow_succ] at he; omega
  rcases he with hpoint | hplane
  · obtain ⟨e⟩ := hpoint
    apply no_units
    apply hasA5TwoResidual_solvable_image h ((determinantCharacter (point k)).comp e.toMonoidHom)
    exact point_determinantCharacter_surjective.comp e.surjective
  · obtain ⟨e⟩ := hplane
    apply no_units
    apply hasA5TwoResidual_solvable_image h ((determinantCharacter (plane k)).comp e.toMonoidHom)
    exact plane_determinantCharacter_surjective.comp e.surjective

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple
