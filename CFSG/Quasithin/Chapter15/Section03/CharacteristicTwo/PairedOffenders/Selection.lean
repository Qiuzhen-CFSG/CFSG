module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.Terminal
public import Theory.Representation.BinaryOffender.Basic

/-!
# Selection of minimal offenders from the source Thompson subgroup

The best-offender and equal-weight lifting clauses of B.2.5 imply that a minimal
nontrivial maximum-elementary image is a minimal best offender. These two clauses
remain explicit inputs; this module does not prove B.2.5.

Sylow conjugacy also transports noncentrality of J(I) to J(S), providing a
nonempty minimal family from a noncentral component of J(I). Only relative
normality of an action kernel is used, through the actual homomorphism.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.5,
printed p.76, and the proof of 15.3.25, printed pp.1133–1134.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Stellmacher Representation.BinaryOffender
variable {G H V : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- B.2.5's best-offender and equal-weight lifting clauses turn minimality
among maximum-elementary images into the source's minimal-best condition. -/
theorem minimal_action_image_isMinimalBest
    (S A : Subgroup G) (f : G →* H) (ρ : Representation (ZMod 2) H V)
    (hA : A ∈ minimalNontrivialActionFamily S f)
    (hbest : ∀ B ∈ elementaryAbelianMaxSubgroups S, B.map f ≠ ⊥ →
      IsBestOffender ρ (B.map f))
    (hlift : ∀ B ∈ elementaryAbelianMaxSubgroups S, ∀ E,
      IsElementaryTwo E → EqualWeightLE ρ E (B.map f) →
      ∃ D ∈ elementaryAbelianMaxSubgroups S, D.map f = E) :
    IsMinimalBestOffender ρ (A.map f) := by
  refine ⟨hbest A hA.1 hA.2.1.1, ?_⟩
  intro B hB hBA
  obtain ⟨D, hD, hDE⟩ := hlift A hA.1 B hB.1 hBA
  exact le_antisymm hBA.1 (hA.2.2 ⟨hB.1.1, D, hD, hDE⟩ hBA.1)

variable [Finite G] [Finite H]

/-- Noncentrality of J(G) supplies a nontrivial maximum-elementary image
in every Sylow two-subgroup. This avoids assuming nonemptiness of B. -/
theorem minimal_action_family_nonempty_of_sylow
    (S : Sylow 2 G) (f : G →* H)
    (hJ : ¬ elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ f.ker) :
    (minimalNontrivialActionFamily (S : Subgroup G) f).Nonempty := by
  apply minimal_action_family_nonempty
  intro hSJ
  apply hJ
  apply sSup_le
  intro A hA
  obtain ⟨T, hAT⟩ := (hA.2.1.isPGroup).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e := MulAut.conj g
  have hTS : (T : Subgroup G).map e.toMonoidHom = (S : Subgroup G) := by
    change ((g • T : Sylow 2 G) : Subgroup G) = (S : Subgroup G)
    rw [hg]
  have hAS : A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup G) := by
    refine ⟨(map_mono hAT).trans hTS.le, hA.2.1.map _, ?_⟩
    intro B _ hB
    rw [card_map_of_injective e.injective]
    exact hA.2.2 B le_top hB
  intro a ha
  have hfix : f (g * a * g⁻¹) = 1 :=
    hSJ ((le_sSup hAS) (mem_map_of_mem e.toMonoidHom ha))
  change f a = 1
  have hh := congrArg (fun x => (f g)⁻¹ * x * f g) hfix
  simpa [map_mul, map_inv, mul_assoc] using hh

/-- Apply Sylow selection to a noncentral subgroup of the actual J(I),
as supplied by the component witness in 15.3.26. -/
theorem minimal_action_family_nonempty_of_component
    (I L : Subgroup G) (S : Sylow 2 I) (f : I →* H)
    (hLJ : L ≤ elementaryAbelianMaxJ I)
    (hL : ¬ L ≤ f.ker.map I.subtype) :
    (minimalNontrivialActionFamily (S : Subgroup I) f).Nonempty := by
  apply minimal_action_family_nonempty_of_sylow S f
  intro hJ
  apply hL
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup I)).map I.subtype =
      elementaryAbelianMaxJ I := by
    rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
      ← MonoidHom.range_eq_map, I.range_subtype]
  exact hLJ.trans (hmap ▸ map_mono hJ)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
