module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.LocalData
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.SourceInputs
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder

/-!
# Cubic generators for the actual source residual

The ordinary natural-line calculation identifies the two-core quotient of
L₁ = O²(N_LT(V₁)) with a group of order three. The quotient comparison
uses the literal permutation map: its restricted kernel lies in O₂(L).
Thus the singleton family {L₁} supplies the simple case.

For the actual covered natural action, the two generators are L₁,+ and L₀.
Their intrinsic two-core quotients have order three, both are normalized
by L₁T, and both are two-perfect by their residual definitions. The earlier
factorization 13.2.2(3) gives generation. The existing marked-product
calculation proves that L₁/O₂(L₁) is elementary abelian of order nine.

`of_models` assembles these branches from just the natural-model alternative
and the covered factorization. `of_earlier` specializes the existing
`Solvable.EarlierLocalInputs` to the genuine standing `LocalSetup`.
These earlier inputs remain explicit: the source assembly must discharge
the local models of §13.2 and 13.5.2 and the factorization 13.2.2(3).
No selected odd subgroup, action alternative or rank obstruction is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.877–878;
standing setup pp.946–947; noncontained branch of 13.8.13, p.951.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial.SourceResiduals
variable {G : Type*} [Group G] [Finite G]

/-- The simple natural-line residual has cubic intrinsic two-core quotient. -/
theorem simple_core_card {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : TransvectionParabolic.EarlierCore.NaturalSetup T L V V₁ V₂ V₃) :
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3 := by
  let Y := TransvectionParabolic.EarlierCore.localResidual L V₁
  let hYL : Y ≤ L := TransvectionParabolic.EarlierCore.localResidual_le L V₁
  let f : Y →* Equiv.Perm (Fin 6) := d.permutation.comp (inclusion (hYL.trans le_sup_left))
  have hr : f.range = d.permutationImage Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion (hYL.trans le_sup_left) y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hk : f.ker = (pCore 2 L).comap (inclusion hYL) := by
    ext y
    change d.permutation (inclusion (hYL.trans le_sup_left) y) = 1 ↔ _
    have he := d.model_compatible (inclusion hYL y)
    change d.permutation (inclusion (hYL.trans le_sup_left) y) = _ at he
    rw [he]
    change ((d.model (QuotientGroup.mk' (pCore 2 L) (inclusion hYL y)) :
      alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        ((1 : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ↔ _
    rw [Subtype.coe_inj, d.model.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hp : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYL)
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = 3 := by
    rw [hr, d.one_image]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder.point_residual_quotient_card
      d.permutation.range d.alternating_le_range d.point d.point_dim
  have he : one L T V₁ = Y := d.line_residual_eq
  rw [he]
  exact (Nat.card_congr
    (Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 f.rangeRestrict
      f.rangeRestrict_surjective hp).toEquiv).trans hc

private theorem elementary_of_card_three {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 3) : IsElementaryAbelian 3 A := by
  let : IsCyclic A := isCyclic_of_prime_card hc
  exact {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      rw [← hc]
      exact pow_card_eq_one' }

/-- In the simple case the single generator is the literal source L₁. -/
noncomputable def simple {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) :
    CubicGeneration (one L T V₁) T where
  generators := {one L T V₁}
  generated := sSup_singleton
  normalizes := by
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact sup_le (one L T V₁).le_normalizer (T_normalizes_one L T V₁ d.line_stable)
  perfect := by
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact residual_isPPerfect _
  cubic := by
    intro X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    exact simple_core_card d.extend
  elementary := elementary_of_card_three (simple_core_card d.extend)

/-- In the covered case the two literal marks generate, each normal in L₁T. -/
noncomputable def covered {L T V V₁ V₃ : Subgroup G}
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    CubicGeneration (one L T V₁) T where
  generators := {plus L T V₁, zero L}
  generated := by rw [sSup_pair, hfactor]
  normalizes := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact sup_le (one_normalizes_plus L T V₁)
        (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable)
    · rcases Set.mem_singleton_iff.mp hX with rfl
      exact sup_le (LocalAction.one_normalizes_zero L T V₁ d.normalizes_L)
        (d.normalizes_L.trans (normalizer_le_zero_normalizer L))
  perfect := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact residual_isPPerfect _
    · rcases Set.mem_singleton_iff.mp hX with rfl
      exact residual_isPPerfect _
  cubic := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact d.plus_core_card hfactor
    · rcases Set.mem_singleton_iff.mp hX with rfl
      exact d.zero_core_card
  elementary := {
    toIsMulCommutative := d.one_quotient_commutative hfactor
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (d.one_quotient_cube hfactor) }

open TransvectionRecognition.Component.ModelExtension

/-- Assemble the two model branches, consuming only the genuine earlier
natural-model alternative and the covered factorization 13.2.2(3). -/
noncomputable def of_models {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (models : Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃))
    (factorization : ∀ _d : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃,
      one L T V₁ = plus L T V₁ ⊔ zero L) :
    CubicGeneration (sourceOne L T V₁) T := by
  classical
  apply Classical.choice
  rcases models with hs | hc
  · exact ⟨simple (Classical.choice hs)⟩
  · let d := Classical.choice hc
    exact ⟨covered d (factorization d)⟩

/-- Apply the local calculations to the standing source setup and its genuine
 earlier model and factorization results. Only `natural_models` and
 `covered_factorization` are consumed; their earlier-source proofs are not
 asserted by this conditional constructor. -/
noncomputable def of_earlier {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G)) :
    CubicGeneration (sourceOne L T V₁) T :=
  of_models (earlier.natural_models T L V V₁ V₂ V₃ M G₁ s)
    (earlier.covered_factorization L T V V₁ V₃)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial.SourceResiduals
end
