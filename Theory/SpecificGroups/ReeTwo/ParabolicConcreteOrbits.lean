module
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLattice

/-!
# Five-centralizers and involution fusion in the actual first parabolics

The conjugators are images under the verified local equivalences, so fusion
occurs inside the stated parabolic. The marked five-centralizer is cyclic
of order four in full Ree, and central of order two in the Tits core. These
are centralizers of the chosen five-subgroup, not of the two-residual.

Source: Aschbacher (1982), (3.2.7) and (3.2.11), as used in
Aschbacher--Smith 14.2.21, p.989.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.ParabolicConcrete
open Centralizer Centralizer.IndexTwo ParabolicMarkedComparison
open Tits.ExceptionalParabolics

/-- The full-Ree orbit Q minus F contains an involution. -/
theorem ree_exists_involution : ∃ x : FullRee.first,
    x ∈ reeQ ∧ orderOf x = 2 ∧ x ∉ reeF := by
  obtain ⟨u,hu,hf⟩ := exists_core_involution_outside_derived_centralizer
  refine ⟨reeCoreMap u, ?_, ?_, ?_⟩
  · rw [← reeCoreMap_range]
    exact ⟨u,rfl⟩
  · exact (orderOf_injective _ reeCoreMap_injective _).trans hu
  · rw [← reeCoreMap_centralizer]
    exact fun h => hf ((mem_map_iff_mem reeCoreMap_injective).mp h)

/-- Any two involutions of Q minus F are conjugate inside the actual full-Ree parabolic. -/
theorem ree_involutions_isConj (x y : FullRee.first) (hxQ : x ∈ reeQ) (hyQ : y ∈ reeQ)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxF : x ∉ reeF) (hyF : y ∉ reeF) : IsConj x y := by
  obtain ⟨u,rfl⟩ := reeCoreMap_range.symm ▸ hxQ
  obtain ⟨v,rfl⟩ := reeCoreMap_range.symm ▸ hyQ
  have hu : u ^ 2 = 1 := reeCoreMap_injective (by simpa only [map_pow, map_one] using hx)
  have hv : v ^ 2 = 1 := reeCoreMap_injective (by simpa only [map_pow, map_one] using hy)
  have huF : u ∉ centralizer (commutator Core : Set Core) :=
    fun h => hxF (reeCoreMap_centralizer ▸ mem_map_of_mem _ h)
  have hvF : v ∉ centralizer (commutator Core : Set Core) :=
    fun h => hyF (reeCoreMap_centralizer ▸ mem_map_of_mem _ h)
  exact Verified.firstEquiv.toMonoidHom.map_isConj (core_involutions_isConj u v hu hv huF hvF)

private theorem tits_mem_Q (x : mixedLocal) : Verified.titsFirstEquiv x ∈ titsQ ↔
    x ∈ pCore 2 mixedLocal := by
  rw [titsQ, ← pCore_map_iso 2 Verified.titsFirstEquiv]
  exact mem_map_iff_mem Verified.titsFirstEquiv.injective

private theorem tits_mem_E (x : mixedLocal) : Verified.titsFirstEquiv x ∈ titsE ↔
    x ∈ ⁅pCore 2 mixedLocal,pCore 2 mixedLocal⁆ := by
  rw [← titsE_eq, ← alternative_derived mixedCharacter (Or.inr rfl)]
  exact mem_map_iff_mem Verified.titsFirstEquiv.injective

/-- The actual Tits orbit Q minus F = E contains an involution. -/
theorem tits_exists_involution : ∃ x : Tits.ExceptionalParabolics.first,
    x ∈ titsQ ∧ orderOf x = 2 ∧ x ∉ titsF := by
  obtain ⟨x,hxQ,hx,hxE⟩ := alternative_exists_involution mixedCharacter (Or.inr rfl)
  refine ⟨Verified.titsFirstEquiv x, (tits_mem_Q x).mpr hxQ,
    (Verified.titsFirstEquiv.orderOf_eq x).trans hx, ?_⟩
  rw [titsF_eq_E]
  exact fun h => hxE ((tits_mem_E x).mp h)

/-- Fusion in the Tits parabolic uses conjugators in the actual mixed kernel. -/
theorem tits_involutions_isConj (x y : Tits.ExceptionalParabolics.first)
    (hxQ : x ∈ titsQ) (hyQ : y ∈ titsQ) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxF : x ∉ titsF) (hyF : y ∉ titsF) : IsConj x y := by
  obtain ⟨u,rfl⟩ := Verified.titsFirstEquiv.surjective x
  obtain ⟨v,rfl⟩ := Verified.titsFirstEquiv.surjective y
  have hu : u ^ 2 = 1 := Verified.titsFirstEquiv.injective (by simpa only [map_pow, map_one] using hx)
  have hv : v ^ 2 = 1 := Verified.titsFirstEquiv.injective (by simpa only [map_pow, map_one] using hy)
  rw [titsF_eq_E] at hxF hyF
  exact Verified.titsFirstEquiv.toMonoidHom.map_isConj
    (alternative_involutions_isConj mixedCharacter (Or.inr rfl) u v
      ((tits_mem_Q u).mp hxQ) ((tits_mem_Q v).mp hyQ) hu hv
      (fun h => hxF ((tits_mem_E u).mpr h)) (fun h => hyF ((tits_mem_E v).mpr h)))

private theorem centralizer_zpowers {A : Type*} [Group A] (g x : A) :
    x ∈ centralizer (zpowers g : Set A) ↔ g * x = x * g := by
  constructor
  · exact fun h => h g (mem_zpowers g)
  · intro h y hy
    obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left h k).eq

/-- The full-Ree fixed subgroup uses exactly source root v5 in the verified coordinates. -/
theorem ree_five_centralizer_comap :
    (centralizer (zpowers reeFive : Set FullRee.first)).comap reeCoreMap =
      zpowers (Core.root 2) := by
  rw [← centralizer_five_comap]
  ext x
  change reeCoreMap x ∈ centralizer (zpowers reeFive : Set FullRee.first) ↔
    (SemidirectProduct.inl x : Centralizer) ∈ centralizer (zpowers fiveGenerator : Set Centralizer)
  rw [centralizer_zpowers, centralizer_zpowers]
  change Verified.firstEquiv fiveGenerator * Verified.firstEquiv (SemidirectProduct.inl x) =
      Verified.firstEquiv (SemidirectProduct.inl x) * Verified.firstEquiv fiveGenerator ↔ _
  rw [← map_mul, ← map_mul]
  exact Verified.firstEquiv.injective.eq_iff

/-- The exact fixed subgroup as a subgroup of the actual full-Ree parabolic. -/
theorem ree_five_centralizer : reeQ ⊓ centralizer (zpowers reeFive : Set FullRee.first) =
    zpowers (Verified.firstEquiv (root 2)) := by
  have h := congrArg (Subgroup.map reeCoreMap) ree_five_centralizer_comap
  rw [map_comap_eq, reeCoreMap_range, MonoidHom.map_zpowers] at h
  change reeQ ⊓ centralizer (zpowers reeFive : Set FullRee.first) =
    zpowers (Verified.firstEquiv (root 2)) at h
  exact h

theorem ree_five_centralizer_card :
    Nat.card (reeQ ⊓ centralizer (zpowers reeFive : Set FullRee.first) : Subgroup FullRee.first) = 4 := by
  rw [ree_five_centralizer, Nat.card_zpowers, Verified.firstEquiv.orderOf_eq]
  change orderOf (SemidirectProduct.inl (Core.root 2) : Centralizer) = 4
  rw [orderOf_injective _ SemidirectProduct.inl_injective]
  exact Core.root_two_order

theorem ree_five_centralizer_cyclic :
    IsCyclic (reeQ ⊓ centralizer (zpowers reeFive : Set FullRee.first) : Subgroup FullRee.first) := by
  rw [ree_five_centralizer]
  infer_instance

/-- The centralizer of the chosen five-subgroup in the actual Tits core. -/
def titsFiveFixed : Subgroup titsQ :=
  (centralizer (zpowers titsFive : Set Tits.ExceptionalParabolics.first)).subgroupOf titsQ

theorem titsFiveFixed_map :
    (fiveFixed mixedLocal (alternative_five_mem mixedCharacter (Or.inr rfl))).map
      titsCoreEquiv.toMonoidHom = titsFiveFixed := by
  ext x
  obtain ⟨x,rfl⟩ := titsCoreEquiv.surjective x
  rw [show titsCoreEquiv x ∈
    (fiveFixed mixedLocal (alternative_five_mem mixedCharacter (Or.inr rfl))).map
      titsCoreEquiv.toMonoidHom ↔ x ∈ fiveFixed mixedLocal
        (alternative_five_mem mixedCharacter (Or.inr rfl)) from
          mem_map_iff_mem titsCoreEquiv.injective]
  change (x : mixedLocal) ∈ centralizer (zpowers (⟨fiveGenerator,
    alternative_five_mem mixedCharacter (Or.inr rfl)⟩ : mixedLocal) : Set mixedLocal) ↔
      (titsCoreEquiv x : Tits.ExceptionalParabolics.first) ∈
        centralizer (zpowers titsFive : Set Tits.ExceptionalParabolics.first)
  rw [centralizer_zpowers, centralizer_zpowers, titsCoreEquiv_val]
  change _ ↔ Verified.titsFirstEquiv _ * Verified.titsFirstEquiv (x : mixedLocal) =
    Verified.titsFirstEquiv (x : mixedLocal) * Verified.titsFirstEquiv _
  rw [← map_mul, ← map_mul]
  exact Verified.titsFirstEquiv.injective.eq_iff.symm

/-- The actual generator is the image of the last root, not the full-Ree v5. -/
theorem titsFiveFixed_eq : titsFiveFixed =
    zpowers (titsCoreEquiv (omegaEquiv mixedCharacter (Or.inr rfl) omegaLastRoot)) := by
  rw [← titsFiveFixed_map, alternative_fiveFixed_eq, MonoidHom.map_zpowers]
  rfl

/-- The Tits fixed-subgroup generator is the same source central involution. -/
theorem titsFiveFixed_generator_mark :
    ((titsCoreEquiv (omegaEquiv mixedCharacter (Or.inr rfl) omegaLastRoot) :
      Tits.ExceptionalParabolics.first) : Tits.Atlas1600Group) = Tits.atlas1600R5 := by
  exact Verified.titsFirstEquiv_last_root

theorem titsFiveFixed_card : Nat.card titsFiveFixed = 2 := by
  rw [← titsFiveFixed_map, ← Nat.card_congr
    ((fiveFixed mixedLocal (alternative_five_mem mixedCharacter (Or.inr rfl))).equivMapOfInjective
      titsCoreEquiv.toMonoidHom titsCoreEquiv.injective).toEquiv]
  exact alternative_fiveFixed_card mixedCharacter (Or.inr rfl)

theorem titsFiveFixed_cyclic : IsCyclic titsFiveFixed := by
  rw [titsFiveFixed_eq]
  infer_instance

theorem titsFiveFixed_le_center : titsFiveFixed ≤ center titsQ := by
  rw [← titsFiveFixed_map]
  rintro _ ⟨x,hx,rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y,rfl⟩ := titsCoreEquiv.surjective y
  change titsCoreEquiv y * titsCoreEquiv x = titsCoreEquiv x * titsCoreEquiv y
  rw [← map_mul, ← map_mul]
  exact congrArg titsCoreEquiv (mem_center_iff.mp
    (alternative_fiveFixed_le_center mixedCharacter (Or.inr rfl) hx) y)

end ReeTwo.ParabolicConcrete
