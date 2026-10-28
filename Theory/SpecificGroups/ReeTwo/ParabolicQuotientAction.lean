module

public import Theory.SpecificGroups.ReeTwo.ParabolicCentralizerOrbits
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.FaithfulSixteen

/-!
# The actual sixteen-point quotient action in the Ree local model

Conjugation in the specified semidirect product induces an action on the
core and then on its quotient by the derived centralizer. The chosen
order-five element moves the coset of the first root, so its image still
has order five. The order-sixteen invariant-subgroup theorem therefore
applies to this particular action.

These are local-model facts, without an assumed ambient Ree identification.
Source: Aschbacher (1982), Section 3, and the verified Shinoda (1975) root
relations in `Core` and `RootAction`; used in quasithin Lemma 14.2.21.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.Centralizer

/-- Conjugation by the local semidirect product on its specified normal core. -/
def coreConjugation : Centralizer →* MulAut Core :=
  SemidirectProduct.lift MulAut.conj Core.complement.subtype (by
    intro a
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    change (a : MulAut Core) x * y * ((a : MulAut Core) x)⁻¹ =
      (a : MulAut Core) (x * (a : MulAut Core).symm y * x⁻¹)
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply])

/-- The core action retains the actual conjugation formula. -/
theorem coreConjugation_apply (g : Centralizer) (x : Core) : coreConjugation g x =
    g.left * (g.right : MulAut Core) x * g.left⁻¹ := rfl

/-- The core action intertwines the actual inclusion with ambient conjugation. -/
theorem inl_coreConjugation (g : Centralizer) (x : Core) :
    (SemidirectProduct.inl (coreConjugation g x) : Centralizer) =
      g * SemidirectProduct.inl x * g⁻¹ := by
  rw [coreConjugation_apply, map_mul, map_mul, map_inv]
  have h := SemidirectProduct.inl_aut (φ := Core.complement.subtype) g.right x
  change (SemidirectProduct.inl ((g.right : MulAut Core) x) : Centralizer) = _ at h
  rw [map_inv] at h
  rw [h]
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  group

/-- The induced action on the quotient by the centralizer of the derived subgroup. -/
def quotientAction : Centralizer →*
    MulAut (Core ⧸ centralizer (commutator Core : Set Core)) :=
  (quotientAut (centralizer (commutator Core : Set Core))).comp coreConjugation

/-- The quotient action is induced by the specified core conjugation. -/
@[simp] theorem quotientAction_mk (g : Centralizer) (x : Core) :
    quotientAction g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (g.left * (g.right : MulAut Core) x * g.left⁻¹) := by
  exact quotientAut_apply_mk _ _ _

/-- The specified five-element remains nontrivial on the actual quotient. -/
theorem quotientAction_five_order : orderOf (quotientAction fiveGenerator) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← fiveGenerator_order, pow_orderOf_eq_one, map_one]
  · intro he
    have hx := DFunLike.congr_fun he (QuotientGroup.mk' _ (Core.root 0))
    rw [quotientAction_mk] at hx
    change QuotientGroup.mk' _ (1 * Core.c (Core.root 0) * 1⁻¹) =
      QuotientGroup.mk' _ (Core.root 0) at hx
    simp only [one_mul, inv_one, mul_one] at hx
    have hh := QuotientGroup.eq.mp hx
    rw [Core.mem_centralizer_derived_iff] at hh
    exact (by decide +kernel : ¬ (
      (Core.c (Core.root 0))⁻¹ * Core.root 0).b0 = 0) hh.1

/-- Five divides the order of the actual quotient action image. -/
theorem five_dvd_quotientAction_range : 5 ∣ Nat.card quotientAction.range := by
  have h := orderOf_dvd_natCard (quotientAction.rangeRestrict fiveGenerator)
  rw [← Subgroup.orderOf_coe] at h
  exact quotientAction_five_order ▸ h

/-- Any local subgroup containing the specified five-element has the same
irreducibility input on this quotient. -/
theorem five_dvd_restricted_quotientAction_range (L : Subgroup Centralizer)
    (hL : fiveGenerator ∈ L) : 5 ∣ Nat.card (quotientAction.comp L.subtype).range := by
  have h := orderOf_dvd_natCard
    ((quotientAction.comp L.subtype).rangeRestrict ⟨fiveGenerator, hL⟩)
  rw [← Subgroup.orderOf_coe] at h
  exact quotientAction_five_order ▸ h

/-- The actual quotient action has no nontrivial proper invariant subgroup. -/
theorem quotientAction_invariant_subgroup
    (D : Subgroup (Core ⧸ centralizer (commutator Core : Set Core)))
    (hD : ∀ g : Centralizer, ∀ v, v ∈ D ↔ quotientAction g v ∈ D) :
    D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five quotientAction
    five_dvd_quotientAction_range Core.quotient_centralizer_derived_card D hD

end ReeTwo.Centralizer
