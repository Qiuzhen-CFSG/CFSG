module
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteStructure

/-!
# Core quotients and conjugation in the marked Ree and Tits parabolics

Actual core inclusions identify the two intrinsic quotients by the derived
centralizer with the computed coordinate quotients. The resulting actions
are conjugation, including on quotient representatives. The marked five
element therefore acts with order five in both cases, proving irreducibility
on the elementary quotient of order sixteen.

Source: Aschbacher--Smith 14.2.21, p.989; Aschbacher (1982), Section 3.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.ParabolicConcrete
open Centralizer Centralizer.IndexTwo ParabolicMarkedComparison
open Tits.ExceptionalParabolics

/-- The ten-root core embedded in the actual full-Ree parabolic. -/
def reeCoreMap : Core →* FullRee.first :=
  Verified.firstEquiv.toMonoidHom.comp (SemidirectProduct.inl : Core →* Centralizer)

theorem reeCoreMap_injective : Function.Injective reeCoreMap :=
  Verified.firstEquiv.injective.comp SemidirectProduct.inl_injective

theorem reeCoreMap_range : reeCoreMap.range = reeQ := by
  rw [reeCoreMap, MonoidHom.range_comp]
  exact Verified.firstEquiv_core

def reeCoreEquiv : Core ≃* reeQ :=
  (MonoidHom.ofInjective reeCoreMap_injective).trans (MulEquiv.subgroupCongr reeCoreMap_range)

@[simp] theorem reeCoreEquiv_val (x : Core) : (reeCoreEquiv x : FullRee.first) = reeCoreMap x := rfl

/-- The intrinsic mixed-kernel core, transported by the actual Tits comparison. -/
def titsCoreEquiv : pCore 2 mixedLocal ≃* titsQ :=
  (Verified.titsFirstEquiv.subgroupMap (pCore 2 mixedLocal)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 Verified.titsFirstEquiv))

@[simp] theorem titsCoreEquiv_val (x : pCore 2 mixedLocal) :
    (titsCoreEquiv x : Tits.ExceptionalParabolics.first) = Verified.titsFirstEquiv x := rfl

private theorem derived_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

private theorem centralizer_derived_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (centralizer (commutator A : Set A)).map e.toMonoidHom =
      centralizer (commutator B : Set B) := by
  rw [← derived_map e]
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem relative_centralizer {A : Type*} [Group A] (Q : Subgroup A) :
    centralizer (commutator Q : Set Q) = (centralizer ((⁅Q,Q⁆ : Subgroup A) : Set A)).subgroupOf Q := by
  rw [← Subgroup.map_subtype_commutator]
  ext x
  constructor
  · intro hx y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact congrArg Subtype.val (hx z hz)
  · intro hx y hy
    exact Subtype.ext (hx (y : A) (mem_map_of_mem _ hy))

abbrev reeV := reeQ ⧸ centralizer (commutator reeQ : Set reeQ)
abbrev titsV := titsQ ⧸ centralizer (commutator titsQ : Set titsQ)

/-- The full-Ree denominator is precisely the relative subgroup F of Q. -/
theorem reeV_denominator : centralizer (commutator reeQ : Set reeQ) = reeF.subgroupOf reeQ :=
  relative_centralizer reeQ

/-- The Tits denominator is precisely the relative subgroup F = E of Q. -/
theorem titsV_denominator : centralizer (commutator titsQ : Set titsQ) = titsF.subgroupOf titsQ :=
  relative_centralizer titsQ

def reeVEquiv : (Core ⧸ centralizer (commutator Core : Set Core)) ≃* reeV :=
  QuotientGroup.congr _ _ reeCoreEquiv (by exact centralizer_derived_map reeCoreEquiv)

def titsVEquiv : CoreQuotient mixedLocal ≃* titsV :=
  QuotientGroup.congr _ _ titsCoreEquiv (by exact centralizer_derived_map titsCoreEquiv)

@[simp] theorem reeVEquiv_mk (x : Core) : reeVEquiv (QuotientGroup.mk' _ x) =
    QuotientGroup.mk' _ (reeCoreEquiv x) := QuotientGroup.congr_mk' _ _ _ _ x

@[simp] theorem titsVEquiv_mk (x : pCore 2 mixedLocal) : titsVEquiv (QuotientGroup.mk' _ x) =
    QuotientGroup.mk' _ (titsCoreEquiv x) := QuotientGroup.congr_mk' _ _ _ _ x

theorem reeV_card : Nat.card reeV = 16 :=
  (Nat.card_congr reeVEquiv.symm.toEquiv).trans Core.quotient_centralizer_derived_card

theorem titsV_card : Nat.card titsV = 16 :=
  (Nat.card_congr titsVEquiv.symm.toEquiv).trans
    (alternative_coreQuotient_card mixedCharacter (Or.inr rfl))

theorem reeV_elementary : IsElementaryAbelian 2 reeV := by
  let := Core.quotient_centralizer_derived_elementary
  exact IsElementaryAbelian.of_surjective reeVEquiv.toMonoidHom reeVEquiv.surjective

theorem titsV_elementary : IsElementaryAbelian 2 titsV := by
  let := alternative_coreQuotient_elementary mixedCharacter (Or.inr rfl)
  exact IsElementaryAbelian.of_surjective titsVEquiv.toMonoidHom titsVEquiv.surjective

/-- The actual conjugation action of the full-Ree parabolic on Q/F. -/
def reeQuotientAction : FullRee.first →* MulAut reeV :=
  (quotientAut (centralizer (commutator reeQ : Set reeQ))).comp MulAut.conjNormal

/-- The actual conjugation action of the Tits parabolic on Q/F. -/
def titsQuotientAction : Tits.ExceptionalParabolics.first →* MulAut titsV :=
  (quotientAut (centralizer (commutator titsQ : Set titsQ))).comp MulAut.conjNormal

@[simp] theorem reeQuotientAction_mk (g : FullRee.first) (x : reeQ) :
    reeQuotientAction g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (MulAut.conjNormal g x) := quotientAut_apply_mk _ _ _

@[simp] theorem titsQuotientAction_mk (g : Tits.ExceptionalParabolics.first) (x : titsQ) :
    titsQuotientAction g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (MulAut.conjNormal g x) := quotientAut_apply_mk _ _ _

private theorem ree_conjugation (g : Centralizer) (x : Core) :
    reeCoreEquiv (coreConjugation g x) = MulAut.conjNormal (Verified.firstEquiv g) (reeCoreEquiv x) := by
  apply Subtype.ext
  change Verified.firstEquiv (SemidirectProduct.inl (coreConjugation g x)) = _
  rw [inl_coreConjugation, map_mul, map_mul, map_inv]
  rfl

private theorem tits_conjugation (g : mixedLocal) (x : pCore 2 mixedLocal) :
    titsCoreEquiv (intrinsicCoreConjugation mixedLocal g x) =
      MulAut.conjNormal (Verified.titsFirstEquiv g) (titsCoreEquiv x) := by
  apply Subtype.ext
  change Verified.titsFirstEquiv (g * (x : mixedLocal) * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The quotient comparison intertwines literal conjugation, not an arbitrary action. -/
theorem ree_action_intertwine (g : Centralizer)
    (v : Core ⧸ centralizer (commutator Core : Set Core)) :
    reeVEquiv (quotientAction g v) = reeQuotientAction (Verified.firstEquiv g) (reeVEquiv v) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ v
  rw [quotientAction_mk, reeVEquiv_mk, reeVEquiv_mk, reeQuotientAction_mk]
  exact congrArg (QuotientGroup.mk' _) (ree_conjugation g x)

theorem tits_action_intertwine (g : mixedLocal) (v : CoreQuotient mixedLocal) :
    titsVEquiv (intrinsicQuotientAction mixedLocal g v) =
      titsQuotientAction (Verified.titsFirstEquiv g) (titsVEquiv v) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ v
  rw [intrinsicQuotientAction_mk, titsVEquiv_mk, titsVEquiv_mk, titsQuotientAction_mk]
  exact congrArg (QuotientGroup.mk' _) (tits_conjugation g x)

/-- The source cyclic-five element, with its verified ambient root-and-Weyl word. -/
def reeFive : FullRee.first := Verified.firstEquiv fiveGenerator

def titsFive : Tits.ExceptionalParabolics.first :=
  Verified.titsFirstEquiv ⟨fiveGenerator, alternative_five_mem mixedCharacter (Or.inr rfl)⟩

theorem reeFive_order : orderOf reeFive = 5 :=
  (Verified.firstEquiv.orderOf_eq _).trans fiveGenerator_order

theorem titsFive_order : orderOf titsFive = 5 := by
  rw [titsFive, Verified.titsFirstEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact fiveGenerator_order

private theorem intertwine_order {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) (b : MulAut B) (h : ∀ x, e (a x) = b (e x)) :
    orderOf b = orderOf a := by
  have he : MulAut.congr e a = b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    simpa using h y
  rw [← he]
  exact (MulAut.congr e).orderOf_eq a

theorem ree_five_action_order : orderOf (reeQuotientAction reeFive) = 5 :=
  (intertwine_order reeVEquiv _ _ (ree_action_intertwine fiveGenerator)).trans
    quotientAction_five_order

theorem tits_five_action_order : orderOf (titsQuotientAction titsFive) = 5 :=
  (intertwine_order titsVEquiv _ _ (tits_action_intertwine
    ⟨fiveGenerator, alternative_five_mem mixedCharacter (Or.inr rfl)⟩)).trans
      (alternative_quotientAction_five_order mixedCharacter (Or.inr rfl))

theorem ree_five_dvd_action : 5 ∣ Nat.card reeQuotientAction.range := by
  have h := orderOf_dvd_natCard (reeQuotientAction.rangeRestrict reeFive)
  rw [← Subgroup.orderOf_coe] at h
  exact ree_five_action_order ▸ h

theorem tits_five_dvd_action : 5 ∣ Nat.card titsQuotientAction.range := by
  have h := orderOf_dvd_natCard (titsQuotientAction.rangeRestrict titsFive)
  rw [← Subgroup.orderOf_coe] at h
  exact tits_five_action_order ▸ h

theorem ree_invariant_subgroup (D : Subgroup reeV)
    (hD : ∀ g : FullRee.first, ∀ v, v ∈ D ↔ reeQuotientAction g v ∈ D) : D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five
    reeQuotientAction ree_five_dvd_action reeV_card D hD

theorem tits_invariant_subgroup (D : Subgroup titsV)
    (hD : ∀ g : Tits.ExceptionalParabolics.first, ∀ v,
      v ∈ D ↔ titsQuotientAction g v ∈ D) : D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five
    titsQuotientAction tits_five_dvd_action titsV_card D hD

end ReeTwo.ParabolicConcrete
