module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerFaithfulness
public import Theory.LinearAlgebra.SmallMultiplicityGroups
/-!
The original faithful full actor has trivial two-core. Its orbit centralizer
therefore vanishes once it is a two-group. A faithful pair of multiplicity
actions of dimensions at most two over F₂ or F₄ supplies that conclusion,
because the actual centralizer order is prime to three and five.

This is the final arithmetic step of the separated A₅ branch in
Aschbacher--Smith D.3.21. Coordinate existence and the multiplicity bound are
independent inputs; the original full/local equality and moved-module consumer
are retained with their literal quotient maps.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A two-group centralizer of the orbit vanishes in the original reduced actor. -/
theorem source_full_actor_orbit_centralizer_eq_bot_of_two :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    IsPGroup 2 (centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))) →
      centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥ := by
  dsimp only
  intro hc
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
  let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hle : centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) ≤
      pCore 2 (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) :=
    le_sSup ⟨inferInstance,hc⟩
  exact le_bot_iff.mp (hle.trans_eq (source_full_module_reduced D).quotient_pCore_eq_bot)


variable (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

include D e in
/-- Small actual multiplicity coordinates kill the full-actor pair centralizer. -/
theorem source_a5_original_actor_centralizer_eq_bot_of_small_multiplicity
    {F₁ F₂ : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let C := centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
    (∃ f : C →* ((Module.End F₁ (Fin k₁ → F₁))ˣ ×
      (Module.End F₂ (Fin k₂ → F₂))ˣ), Function.Injective f) → C = ⊥ := by
  dsimp only
  rintro ⟨f,hf⟩
  have hc := source_a5_original_actor_centralizer_coprime D e hn ht htn
  exact source_full_actor_orbit_centralizer_eq_bot_of_two D
    (Theory.LinearAlgebra.SmallMultiplicityGroups.isPGroup_two_of_injective_unit_pair
      hF₁ hF₂ hk₁ hk₂ f hf hc.1 hc.2)

include D e in
/-- Small commuting multiplicity coordinates feed the original full/local equality. -/
theorem source_a5_full_eq_local_of_small_multiplicity
    {F₁ F₂ : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      let C := centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
      ∃ f : C →* ((Module.End F₁ (Fin k₁ → F₁))ˣ ×
        (Module.End F₂ (Fin k₂ → F₂))ˣ), Function.Injective f) :
    D.fullModule = D.moduleSubgroup :=
  source_a5_full_eq_local_of_actor_pair_centralizer_eq_bot D e hn ht htn
    (source_a5_original_actor_centralizer_eq_bot_of_small_multiplicity D e
      hF₁ hF₂ hk₁ hk₂ hn ht htn hcoords)

open scoped IsMulCommutative
local instance originalCentralizerControlMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The same small multiplicity coordinates conclude the original source consumer. -/
theorem source_a5_original_irreducible_of_small_multiplicity
    {F₁ F₂ : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hF₁ : Nat.card F₁ = 2 ∨ Nat.card F₁ = 4)
    (hF₂ : Nat.card F₂ = 2 ∨ Nat.card F₂ = 4)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2) (hk₂ : k₂ ≤ 2)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hcoords : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      let C := centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
      ∃ f : C →* ((Module.End F₁ (Fin k₁ → F₁))ˣ ×
        (Module.End F₂ (Fin k₂ → F₂))ˣ), Function.Injective f) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_separated_seed D hn ht htn e
    (source_a5_full_eq_local_of_small_multiplicity D e hF₁ hF₂ hk₁ hk₂ hn ht htn hcoords) hsep

end CFSG.Quasithin.Chapter10
