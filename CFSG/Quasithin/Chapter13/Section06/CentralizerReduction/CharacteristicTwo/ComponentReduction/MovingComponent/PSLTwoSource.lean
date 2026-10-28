module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualSource

/-!
# The actual cubic residual and moving Suzuki pair

The rank-one case of 1.2.2(a), applied to the literal component of C_G(v),
identifies its two-conjugate span with O^{3′}(C_G(v)). The quasithin rank
bound is inherited from the original nontrivial local two-core. Thus the
marked involution excludes binary PSL₂, and the full model comparison
constructs the paired Suzuki action. Neither a universal residual theorem
nor the separate A.3.18 alternatives are assumed.

Source: Aschbacher--Smith 1.2.2(a), printed p.504, and 13.6.6, p.927.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open A5Module InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

theorem source_psl2_residual_exact (d : Setup κ T s)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hpsl : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m)) :
    primeToResidual 3 (Gv (markedV s)) =
      componentOrbit K (localT (T : Subgroup G) (markedV s)) := by
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp i.moving
  rw [orbit_eq_pair K _ hi ht htn]
  let e := ModelComparison.componentTwoCoreEquivImage i.oddCore i.component
  let : IsSimpleGroup (NormalizerAction.componentImage K) :=
    ModelComparison.componentImage_simple i.component
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let : IsQuasisimple K := i.component.2
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective (pCore 2 K))
  have hHN : Gv (markedV s) ≤ normalizer ((Gv (markedV s)).pCoreIn 2 : Set G) :=
    (Gv (markedV s)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (Gv (markedV s))))
  have hlocal := (d.ambient.twoLocal_sqtk
    (show IsTwoLocal (normalizer ((Gv (markedV s)).pCoreIn 2 : Set G)) from
      ⟨_, d.local115.mem_H, isPGroup_pCoreIn 2 _, rfl⟩)).stronglyQuasithin.of_injective
        (inclusion hHN) (inclusion_injective hHN)
  exact (Chapter1.Section02.rankOne_pair_eq_primeToResidual_three
    i.component.isCComponent hi t htn
    (ModelComparison.psl2_three_divides_quotients i.oddCore i.component hpsl).2.1
    (hlocal 3 Nat.prime_three (by decide)) (Or.inl ⟨m, hpsl.of_mulEquiv e⟩)).symm

theorem not_psl2_of_original_source (d : Setup κ T s)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    ¬ ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m) := by
  intro hpsl
  have hres := source_psl2_residual_exact d i hpsl
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  have hKD : ⁅K, residual s⁆ ≠ ⊥ := by
    rw [i.action.commutator_residual]
    exact i.component.isCComponent.ne_bot
  obtain ⟨a, ha, _, haC⟩ := exists_marked_involution d i
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact exclude_psl2_of_cubic_residual s (T : Subgroup G) K i.component hi i.moving
    i.action.residual_normalizes hcard hres hKD a ha haC e

theorem exists_suzukiPair_of_original_source (d : Setup κ T s)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    ∃ c : SuzukiPairConfiguration s (T : Subgroup G) K i.action.residual_normalizes,
      m = 2 * c.parameter + 1 ∧ 3 ∣ m := by
  have comparison := ModelComparison.source_comparison i
  obtain ⟨n, hn, hm, ⟨e₀⟩⟩ := comparison.model.resolve_left
    (not_psl2_of_original_source d i hcard)
  have hKD : ⁅K, residual s⁆ ≠ ⊥ := by
    rw [i.action.commutator_residual]
    exact i.component.isCComponent.ne_bot
  obtain ⟨eK, ⟨cubic⟩⟩ := exists_cubicFieldAction K (residual s) i.component
    i.action.residual_normalizes (residual_twoPerfect s) hcard hKD n hn e₀
  obtain ⟨coordinates⟩ := exists_pairCoordinates K (localT (T : Subgroup G) (markedV s))
    i.component comparison.index i.moving eK
  exact ⟨⟨n, hn, eK, coordinates, cubic⟩, hm, hm.symm ▸ cubic.three_dvd_degree⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
