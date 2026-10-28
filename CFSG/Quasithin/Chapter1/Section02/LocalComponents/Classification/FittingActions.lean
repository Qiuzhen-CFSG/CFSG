module

public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini
public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini.ActionTransport
public import Theory.Frattini.NilpotentProducts
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions

/-!
# Genuine full-core Frattini actions in the odd A.3.6 alternatives

Conjugation on `Oₚ(K)/Φ(Oₚ(K))` is intertwined with the existing action on
`Ω₁(Oₚ(K))/Φ(Ω₁(Oₚ(K)))`. In the homocyclic case the isomorphism is the
natural power bridge, including every higher exponent; in the exponent-p
case it comes from the inclusion of omega. The embedded omega comparison
uses the original core inclusion, so the resulting actions are the actual
K-actions.

The previously proved strengthened omega actions give the common Fitting
kernel, full-group and Sylow-two irreducibility, and quaternion images on
these individual prime quotients. Perfectness and the nilpotent A.3.6
alternative also imply that every element of order two in the actual K/F(K)
inverts each core Frattini quotient. The SL₂(5) scalar-involution calculation
is checked by the kernel over the finite concrete matrix model.

The canonical prime-core inclusions carry their Frattini subgroups into
Φ(F(K)) and generate F(K). Their equivariant quotient maps therefore assemble
primewise inversion on the full mixed-prime quotient F(K)/Φ(F(K)).
Irreducibility is asserted only on the individual prime quotients.
No center–Frattini equality or exponent-one assumption is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 and its
proof, printed pp.43–45, and the first paragraph of the proof of 13.1.9,
printed p.869. The Chapter 13 owner must still identify its ambient element
with this order-two element of the Fitting quotient.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.RadicalActions
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.FittingActions

variable {K : Type*} [Group K]

/-- Conjugation on the actual characteristic prime core. -/
def coreAction (p : ℕ) (K : Type*) [Group K] : K →* MulAut (pCore p K) :=
  (MulAut.characteristic (pCore p K)).comp MulAut.conj

/-- Conjugation on the Frattini quotient of the full prime core. -/
def coreFrattiniAction (p : ℕ) (K : Type*) [Group K] :
    K →* MulAut (pCore p K ⧸ frattini (pCore p K)) :=
  (quotientAut (frattini (pCore p K))).comp (coreAction p K)

theorem coreAction_apply (p : ℕ) (g : K) (x : pCore p K) :
    (coreAction p K g x : K) = g * x * g⁻¹ := rfl

theorem coreFrattiniAction_apply_mk (p : ℕ) (g : K) (x : pCore p K) :
    coreFrattiniAction p K g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (coreAction p K g x) := by
  exact quotientAut_apply_mk _ _ _

/-- Conjugation on the actual Fitting subgroup, for the mixed-prime assembly. -/
def fittingAction (K : Type*) [Group K] : K →* MulAut (fittingSubgroup K) :=
  (MulAut.characteristic (fittingSubgroup K)).comp MulAut.conj

/-- Conjugation on the actual Fitting Frattini quotient. -/
def fittingFrattiniAction (K : Type*) [Group K] :
    K →* MulAut (fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :=
  (quotientAut (frattini (fittingSubgroup K))).comp (fittingAction K)

theorem fittingAction_apply (g : K) (x : fittingSubgroup K) :
    (fittingAction K g x : K) = g * x * g⁻¹ := rfl

theorem fittingFrattiniAction_apply_mk (g : K) (x : fittingSubgroup K) :
    fittingFrattiniAction K g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (fittingAction K g x) := by
  exact quotientAut_apply_mk _ _ _

/-- The intrinsic omega subgroup with its original embedding in K. -/
noncomputable def embeddedOmegaEquiv (p : ℕ) (K : Type*) [Group K] :
    omega (pCore p K) (p := p) 1 ≃* omegaCore p K :=
  (omega (pCore p K) (p := p) 1).equivMapOfInjective
    (pCore p K).subtype (pCore p K).subtype_injective

/-- The Frattini comparison induced by the original omega embedding. -/
noncomputable def embeddedOmegaFrattiniEquiv (p : ℕ) (K : Type*) [Group K] :
    (omega (pCore p K) (p := p) 1 ⧸ frattini (omega (pCore p K) (p := p) 1)) ≃*
      (omegaCore p K ⧸ frattini (omegaCore p K)) :=
  QuotientGroup.congr _ _ (embeddedOmegaEquiv p K) (frattini_map_equiv _)

theorem embeddedOmegaFrattiniEquiv_equivariant (p : ℕ) (g : K)
    (z : omega (pCore p K) (p := p) 1 ⧸ frattini (omega (pCore p K) (p := p) 1)) :
    embeddedOmegaFrattiniEquiv p K
      (quotientAut (frattini (omega (pCore p K) (p := p) 1))
        (OmegaAction.omegaRestriction (pCore p K) p 1 (coreAction p K g)) z) =
      omegaFrattiniAction p K g (embeddedOmegaFrattiniEquiv p K z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' _ _ = quotientAut _ _ (QuotientGroup.mk' _ _)
  rw [quotientAut_apply_mk]
  rfl

open GroupActionTransport


variable [Finite K] {p : ℕ} [Fact p.Prime]

/-- Both source core shapes give an equivariant isomorphism of actual quotients. -/
theorem exists_coreOmegaEquiv (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    ∃ e : (pCore p K ⧸ frattini (pCore p K)) ≃*
      (omegaCore p K ⧸ frattini (omegaCore p K)),
      ∀ g z, e (coreFrattiniAction p K g z) = omegaFrattiniAction p K g (e z) := by
  have hx : ∃ e : (pCore p K ⧸ frattini (pCore p K)) ≃*
      (omega (pCore p K) (p := p) 1 ⧸ frattini (omega (pCore p K) (p := p) 1)),
      ∀ α z, e (quotientAut (frattini (pCore p K)) α z) =
        quotientAut (frattini (omega (pCore p K) (p := p) 1))
          (OmegaAction.omegaRestriction (pCore p K) p 1 α) (e z) := by
    obtain ⟨_, _, he | he | he⟩ := RadicalStructure.radical_core h hd
    · let := he.1
      have hexp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (pCore p K))
      exact ⟨HomocyclicOmegaFrattini.exponentQuotientEquiv p hexp,
        HomocyclicOmegaFrattini.exponentQuotientEquiv_equivariant p hexp⟩
    · exact ⟨HomocyclicOmegaFrattini.exponentQuotientEquiv p he.2,
        HomocyclicOmegaFrattini.exponentQuotientEquiv_equivariant p he.2⟩
    · obtain ⟨a, ha, ⟨e⟩⟩ := he
      exact ⟨HomocyclicOmegaFrattini.quotientEquiv ha e,
        HomocyclicOmegaFrattini.quotientEquiv_equivariant ha e⟩
  obtain ⟨e, he⟩ := hx
  refine ⟨e.trans (embeddedOmegaFrattiniEquiv p K), ?_⟩
  intro g z
  change embeddedOmegaFrattiniEquiv p K
    (e (quotientAut (frattini (pCore p K)) (coreAction p K g) z)) = _
  rw [he, embeddedOmegaFrattiniEquiv_equivariant]
  rfl

/-- A choice of the proved natural comparison of the actual core quotients. -/
noncomputable def coreOmegaEquiv (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    (pCore p K ⧸ frattini (pCore p K)) ≃*
      (omegaCore p K ⧸ frattini (omegaCore p K)) :=
  (exists_coreOmegaEquiv h hd).choose

/-- The chosen comparison intertwines the original K-actions. -/
theorem coreOmegaEquiv_equivariant (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (g : K)
    (z : pCore p K ⧸ frattini (pCore p K)) :
    coreOmegaEquiv h hd (coreFrattiniAction p K g z) =
      omegaFrattiniAction p K g (coreOmegaEquiv h hd z) :=
  (exists_coreOmegaEquiv h hd).choose_spec g z


/-- The quotient actions have identical kernels, through the natural power bridge. -/
theorem core_action_ker_eq_omega (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    (coreFrattiniAction p K).ker = (omegaFrattiniAction p K).ker :=
  equivariant_ker_eq _ _ (coreOmegaEquiv h hd) (coreOmegaEquiv_equivariant h hd)

/-- The actual restricted action images are isomorphic, including on Sylow subgroups. -/
noncomputable def coreActionRangeEquiv (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Subgroup K) :
    ((coreFrattiniAction p K).comp S.subtype).range ≃*
      ((omegaFrattiniAction p K).comp S.subtype).range := by
  exact equivariantRangeEquiv _ _ (coreOmegaEquiv h hd)
    (fun s z => coreOmegaEquiv_equivariant h hd s z)

/-- Every irreducible omega action transports to the full core Frattini quotient. -/
theorem core_action_irreducible (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K))
    (hi : ∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ g x, x ∈ A → omegaFrattiniAction p K g x ∈ A) → A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (pCore p K ⧸ frattini (pCore p K)),
      (∀ g x, x ∈ A → coreFrattiniAction p K g x ∈ A) → A = ⊥ ∨ A = ⊤ :=
  equivariant_irreducible _ _ (coreOmegaEquiv h hd) (coreOmegaEquiv_equivariant h hd) hi

/-- Sylow irreducibility and quaternion subgroups transfer through the same isomorphism. -/
theorem core_sylow_actions (h : A36Natural K ∨ A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K)
    (hs : (∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
        (∀ s : S, ∀ x ∈ A, omegaFrattiniAction p K s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range,
        Function.Injective f) :
    (∀ A : Subgroup (pCore p K ⧸ frattini (pCore p K)),
        (∀ s : S, ∀ x ∈ A, coreFrattiniAction p K s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      ∃ f : QuaternionGroup 2 →*
        ((coreFrattiniAction p K).comp (S : Subgroup K).subtype).range,
        Function.Injective f := by
  constructor
  · exact equivariant_irreducible
      ((coreFrattiniAction p K).comp (S : Subgroup K).subtype)
      ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype)
      (coreOmegaEquiv h hd) (fun s z => coreOmegaEquiv_equivariant h hd s z) hs.1
  · obtain ⟨f, hf⟩ := hs.2
    let e := coreActionRangeEquiv h hd (S : Subgroup K)
    exact ⟨e.symm.toMonoidHom.comp f, e.symm.injective.comp hf⟩

/-- The actual full-core analog of the strengthened omega-action data. -/
def FrattiniActionData (B : Type*) [Group B] : Prop :=
  generalizedFitting B = fittingSubgroup B ∧
    fittingSubgroup B = pPrimeCore 2 B ∧
    ∀ (r : ℕ) [Fact r.Prime], r ∣ Nat.card (fittingSubgroup B) →
      3 < r ∧ (coreFrattiniAction r B).ker = fittingSubgroup B ∧
      (∀ A : Subgroup (pCore r B ⧸ frattini (pCore r B)),
        (∀ b : B, ∀ a ∈ A, coreFrattiniAction r B b a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      (∀ S : Sylow 2 B,
        (∀ A : Subgroup (pCore r B ⧸ frattini (pCore r B)),
          (∀ s : S, ∀ a ∈ A, coreFrattiniAction r B s a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
        ∃ f : QuaternionGroup 2 →*
          ((coreFrattiniAction r B).comp (S : Subgroup B).subtype).range,
          Function.Injective f)

/-- Transport of the full earlier omega-action data, prime by prime. -/
theorem frattiniActionData_of_omega (h : A36Natural K ∨ A36Nilpotent K)
    (hw : CenterFrattiniSource.OmegaActionData K) : FrattiniActionData K := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  intro p _ hd
  obtain ⟨hp, hk, hi, hs⟩ := hw.2.2 p hd
  exact ⟨hp, (core_action_ker_eq_omega h hd).trans hk,
    core_action_irreducible h hd hi, fun S => core_sylow_actions h hd S (hs S)⟩

universe u
/-- Source A.3.6 retains all structural alternatives and gives the actual
full-core Frattini actions, with no additional action hypothesis. -/
theorem strengthened_frattini_actions
    {𝒦 : GroupClass.{u}} {E : Type u} [Group E] [Finite E]
    (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent) (h : A36Conclusion C) :
    A36Conclusion C ∧ (¬ IsQuasisimple C → FrattiniActionData C) := by
  refine ⟨h, fun hn => ?_⟩
  exact frattiniActionData_of_omega (RadicalStructure.nonsimple_radical h hn)
    ((CenterFrattiniSource.strengthened_omega_actions hE hO hC h).2 hn)

/-- The nilpotent core actions under precisely the intrinsic perfect-group hypotheses. -/
theorem nilpotent_frattini_actions [Group.IsPerfect K]
    (hn : A36Nilpotent K) (hc : A36Common K) : FrattiniActionData K := by
  apply frattiniActionData_of_omega (Or.inr hn)
  refine ⟨hn.1, hc.1, ?_⟩
  intro p _ hd
  have hp := (RadicalStructure.radical_core (Or.inr hn) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hs := CenterFrattiniSource.nilpotent_sylow_actions hn ho hd
  let S : Sylow 2 K := Classical.arbitrary _
  have hQ : ∃ f : QuaternionGroup 2 →* (omegaFrattiniAction p K).range,
      Function.Injective f := by
    obtain ⟨f, hf⟩ := (hs S).2
    have hle : ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range ≤
        (omegaFrattiniAction p K).range := by
      rintro x ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    exact ⟨(inclusion hle).comp f, (inclusion_injective hle).comp hf⟩
  exact ⟨hp, CenterFrattiniSource.nilpotent_action_ker_eq_fitting hn hc hd hQ,
    fun A hA => (hs S).1 A (fun s x hx => hA s x hx), hs⟩


private theorem sl2_five_square :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), g ^ 2 = 1 → g = 1 ∨ g = -1 := by
  decide +kernel

/-- An element of order two in the actual Fitting quotient inverts the
Frattini quotient of every odd core. The homocyclic exponent remains arbitrary. -/
theorem nilpotent_core_inversion [Group.IsPerfect K]
    (hn : A36Nilpotent K) (hd : p ∣ Nat.card (fittingSubgroup K))
    (t : K) (ht : orderOf (QuotientGroup.mk' (fittingSubgroup K) t) = 2)
    (x : pCore p K ⧸ frattini (pCore p K)) :
    coreFrattiniAction p K t x = x⁻¹ := by
  have hp := (RadicalStructure.radical_core (Or.inr hn) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  obtain ⟨e, he⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient hn ho hd
  let z := QuotientGroup.mk' (generalizedFitting K) t
  let c := QuotientGroup.quotientMulEquivOfEq hn.1
  have hcz : c z = QuotientGroup.mk' (fittingSubgroup K) t := rfl
  have hz : orderOf z = 2 := by rw [← c.orderOf_eq z, hcz]; exact ht
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hez2 : (e z) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hez : e z = -1 := by
    apply (sl2_five_square (e z) hez2).resolve_left
    intro h
    have hz1 : z = 1 := e.injective (h.trans e.map_one.symm)
    rw [hz1, orderOf_one] at hz
    omega
  have homega (y : omegaCore p K ⧸ frattini (omegaCore p K)) :
      omegaFrattiniAction p K t y = y⁻¹ := by
    have hsymm : e.symm (-1) = z := by rw [← hez, e.symm_apply_apply]
    simpa only [hsymm, z, RadicalActions.Nilpotent.quotientAction_apply_mk] using he y
  apply (coreOmegaEquiv (Or.inr hn) hd).injective
  rw [coreOmegaEquiv_equivariant, homega, map_inv]

/-- In the nilpotent A.3.6 alternative, every element whose image in the
actual K/F(K) has order two inverts the full Fitting Frattini quotient.
The prime-core action premises are discharged by `nilpotent_core_inversion`;
the mixed-prime assembly uses the canonical core inclusions. -/
theorem nilpotent_fitting_inversion [Group.IsPerfect K]
    (hn : A36Nilpotent K)
    (t : K) (ht : orderOf (QuotientGroup.mk' (fittingSubgroup K) t) = 2)
    (x : fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :
    fittingFrattiniAction K t x = x⁻¹ := by
  exact FittingFrattini.quotientAut_inverts K (MulAut.conj t)
    (fun p _ hd z => nilpotent_core_inversion hn hd t ht z) x

end CFSG.Quasithin.Chapter1.Section02.FittingActions
