module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo
public import Theory.SpecificGroups.ReeTwo.ParabolicLinearAction

/-!
# Structure of the actual marked binary Ree and Tits first parabolics

The verified root-and-Weyl equivalences transport the intrinsic calculations
into the first parabolic in `ReeF4.Model 0` and its specified Atlas Tits
intersection. All derived subgroups below are formed from the intrinsic
two-core of that actual local group. The mixed character kernel, selected by
the verified ambient embedding, has self-centralizing derived subgroup; the
full Ree local group has the larger order-64 centralizer.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989; Aschbacher (1982),
Section 3, especially (3.2.7) and (3.2.11); Parrott (1972), p.672.
The incorrect quotient-center and residual-centralizer formulas in the
printed argument are not used.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.ParabolicConcrete
open Centralizer Centralizer.IndexTwo ParabolicMarkedComparison
open Tits.ExceptionalParabolics

abbrev reeQ : Subgroup FullRee.first := pCore 2 FullRee.first
abbrev reeE : Subgroup FullRee.first := ⁅reeQ, reeQ⁆
abbrev reeF : Subgroup FullRee.first := centralizer (reeE : Set FullRee.first)
abbrev titsQ : Subgroup Tits.ExceptionalParabolics.first := pCore 2 Tits.ExceptionalParabolics.first
abbrev titsE : Subgroup Tits.ExceptionalParabolics.first := ⁅titsQ, titsQ⁆
abbrev titsF : Subgroup Tits.ExceptionalParabolics.first :=
  centralizer (titsE : Set Tits.ExceptionalParabolics.first)

private theorem centralizer_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) :
    (centralizer (D : Set A)).map e.toMonoidHom =
      centralizer (D.map e.toMonoidHom : Set B) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem card_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) : Nat.card (D.map e.toMonoidHom) = Nat.card D :=
  (Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm

/-- The full-Ree derived subgroup is the image of the computed tail. -/
theorem reeE_eq : derived.map Verified.firstEquiv.toMonoidHom = reeE := by
  rw [derived_eq_core_commutator, map_commutator, Verified.firstEquiv_core]

/-- The Tits derived subgroup is the image of the same tail in the mixed kernel. -/
theorem titsE_eq : (derived.subgroupOf mixedLocal).map Verified.titsFirstEquiv.toMonoidHom =
    titsE := by
  rw [← alternative_derived mixedCharacter (Or.inr rfl), map_commutator, pCore_map_iso]

/-- The full-Ree centralizer is transported with its literal ambient conjugation. -/
theorem reeF_eq : (centralizer (derived : Set Centralizer)).map
    Verified.firstEquiv.toMonoidHom = reeF := by
  rw [centralizer_map, reeE_eq]

/-- The relative action kernel maps to the actual Tits derived centralizer. -/
theorem titsF_eq : (derivedCentralizerIn mixedLocal).map
    Verified.titsFirstEquiv.toMonoidHom = titsF := by
  rw [derivedCentralizerIn_eq_centralizer mixedLocal
    (derived_le_omega.trans (omega_le_kernel mixedCharacter (Or.inr rfl))),
    centralizer_map, titsE_eq]

/-- The first two-core in full Ree has order 1024. -/
theorem reeQ_card : Nat.card reeQ = 1024 := by
  rw [reeQ, ← Verified.firstEquiv_core, card_map]
  exact core_card

/-- The first Tits two-core has order 512, not the full coordinate core. -/
theorem titsQ_card : Nat.card titsQ = 512 := by
  rw [titsQ, ← pCore_map_iso 2 Verified.titsFirstEquiv, card_map]
  exact alternative_pCore_card mixedCharacter (Or.inr rfl)

theorem reeE_card : Nat.card reeE = 32 := by
  rw [← reeE_eq, card_map]
  exact derived_card

theorem titsE_card : Nat.card titsE = 32 := by
  rw [← titsE_eq, ← alternative_derived mixedCharacter (Or.inr rfl), card_map]
  exact alternative_derived_card mixedCharacter (Or.inr rfl)

theorem reeE_elementary : IsElementaryAbelian 2 reeE := by
  rw [← reeE_eq]
  let := derived_elementary
  exact IsElementaryAbelian.map _

theorem titsE_elementary : IsElementaryAbelian 2 titsE := by
  rw [← titsE_eq, ← alternative_derived mixedCharacter (Or.inr rfl)]
  let := alternative_derived_elementary mixedCharacter (Or.inr rfl)
  exact IsElementaryAbelian.map _

/-- In the actual Tits local group F = E. -/
theorem titsF_eq_E : titsF = titsE := by
  rw [titsF, ← titsE_eq, ← centralizer_map, ← alternative_derived mixedCharacter (Or.inr rfl),
    alternative_centralizer_derived mixedCharacter (Or.inr rfl)]

/-- In full Ree the additional factor is the actual image of source root v5. -/
theorem reeF_eq_sup : reeF = zpowers (Verified.firstEquiv (root 2)) ⊔ reeE := by
  rw [← reeF_eq, centralizer_derived_eq_sup, Subgroup.map_sup, MonoidHom.map_zpowers, reeE_eq]
  rfl

theorem reeF_card : Nat.card reeF = 64 := by
  rw [← reeF_eq, card_map]
  exact centralizer_derived_card

theorem titsF_card : Nat.card titsF = 32 := by rw [titsF_eq_E, titsE_card]

theorem reeF_le_Q : reeF ≤ reeQ := by
  rw [← reeF_eq, reeQ, ← Verified.firstEquiv_core]
  exact map_mono derivedCentralizer_le_core

theorem titsF_le_Q : titsF ≤ titsQ := by
  rw [titsF_eq_E]
  exact commutator_le_left _ _

/-- The full-Ree quotient is the actual C5:C4 complement via the marked core map. -/
def reeQuotientEquiv : (FullRee.first ⧸ reeQ) ≃* FiveFour.Group :=
  Verified.firstQuotientEquiv.symm.trans quotientCoreEquiv

/-- The actual Tits quotient uses the order-512 mixed-kernel core. -/
def titsQuotientEquiv : (Tits.ExceptionalParabolics.first ⧸ titsQ) ≃* FiveFour.Group :=
  (QuotientGroup.congr _ _ Verified.titsFirstEquiv
    (pCore_map_iso 2 Verified.titsFirstEquiv)).symm.trans
      (alternativeQuotientEquiv mixedCharacter (Or.inr rfl))

theorem ree_quotient_card : Nat.card (FullRee.first ⧸ reeQ) = 20 :=
  (Nat.card_congr reeQuotientEquiv.toEquiv).trans FiveFour.card

theorem tits_quotient_card : Nat.card (Tits.ExceptionalParabolics.first ⧸ titsQ) = 20 :=
  (Nat.card_congr titsQuotientEquiv.toEquiv).trans FiveFour.card

private theorem sylow_cyclic {A : Type*} [Group A] [Finite A]
    (e : A ≃* FiveFour.Group) (T : Sylow 2 A) : IsCyclic T := by
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let := fiveFour_sylowTwo_cyclic S
  let f : T ≃* S := T.toSubgroup.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_injective f.toMonoidHom f.injective

theorem ree_quotient_sylow_cyclic (T : Sylow 2 (FullRee.first ⧸ reeQ)) : IsCyclic T :=
  sylow_cyclic reeQuotientEquiv T

theorem tits_quotient_sylow_cyclic (T : Sylow 2 (Tits.ExceptionalParabolics.first ⧸ titsQ)) :
    IsCyclic T := sylow_cyclic titsQuotientEquiv T

end ReeTwo.ParabolicConcrete
