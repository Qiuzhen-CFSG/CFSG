module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Common kernels for the actual A.3.6 omega actions

For each odd Fitting prime p, the action is conjugation on
Ω₁(Oₚ(B))/Φ(Ω₁(Oₚ(B))). In the natural case this omega subgroup equals the
Fitting subgroup and its Frattini subgroup is trivial; the source component
centralizer theorem identifies the kernel. In the nilpotent case a quaternion
subgroup of the action image exhausts the two-part of B/F(B), whose order is
120. The normal kernel is consequently odd, so it lies in F(B) = O₂'(B).
Every prime core already acts trivially, proving equality of these kernels.

`strengthened_omega_actions` retains every A.3.6 assertion and adds the
whole-component and Sylow irreducibility statements and exact common kernel.
The natural branch uses the existing matrix proof. The nilpotent branch uses
perfectness to prove nontriviality, then the degree-two SL₂(5) theorem to prove
central inversion. All action premises in the intermediate conditional
assembly are discharged. The quotient-to-image equivalence includes its
conjugation equation, tying the source SL₂ quotient to the actual action.

`strengthened_A36_of_A36` is the universal interface for the radical consumer.
It takes only the original A.3.6 classification as earlier-source input; that
classification remains the upstream owner's responsibility.

When only one odd prime divides F(B), the common kernel gives
C_B(Ω₁(Oₚ(B))) ≤ Oₚ(B), including the extraspecial case. All homocyclic
exponents are retained. No center–Frattini equality is used.

The nilpotent order argument also occurs privately in
`Radical.Normalizers.Residual.Actions.RelativeKernel`; here it is exposed at
the intrinsic component-action interface for the strengthened source assembly.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 and proof,
printed pp.43–45, and the radical construction and actions, pp.509, 513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

omit [Finite K] [Fact p.Prime] in
theorem omega_centralizer_le_action_ker :
    centralizer (omegaCore p K : Set K) ≤ (omegaFrattiniAction p K).ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini (omegaCore p K)) v
  change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K g)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  rw [omegaCoreAction_apply, ← mem_centralizer_iff.mp hg x x.property,
    mul_inv_cancel_right]

omit [Finite K] [Fact p.Prime] in
private theorem action_ker_eq_centralizer (hf : frattini (omegaCore p K) = ⊥) :
    (omegaFrattiniAction p K).ker = centralizer (omegaCore p K : Set K) := by
  apply le_antisymm _ omega_centralizer_le_action_ker
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  let q := QuotientGroup.mk' (frattini (omegaCore p K))
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk', hf])
  have he : omegaCoreAction p K g ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply hq
    have hh := congrArg (fun f : MulAut (omegaCore p K ⧸ frattini (omegaCore p K)) =>
      f (q ⟨x, hx⟩)) (MonoidHom.mem_ker.mp hg)
    change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K g)
      (QuotientGroup.mk' _ ⟨x, hx⟩) = q ⟨x, hx⟩ at hh
    rwa [quotientAut_apply_mk] at hh
  have hh : g * x * g⁻¹ = x := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem natural_omega (h : A36Natural K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    omegaCore p K = fittingSubgroup K ∧ IsElementaryAbelian p (omegaCore p K) := by
  obtain ⟨hF, r, hr, _, ha⟩ := h
  obtain ⟨he, hc⟩ := RadicalStructure.natural_elementary ha
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ r ^ 2 by
      simpa only [← hF, hc] using hd))
  subst r
  have hfit : fittingSubgroup K = pCore p K := RadicalStructure.fitting_eq_core (by
    rw [← hF]; exact IsPGroup.of_card hc)
  have hGF : generalizedFitting K = pCore p K := hF.trans hfit
  let : IsElementaryAbelian p (pCore p K) := hGF ▸ he
  have hw : omegaCore p K = pCore p K := by
    unfold omegaCore
    rw [RadicalStructure.omega_top (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (pCore p K))),
      ← MonoidHom.range_eq_map, range_subtype]
  exact ⟨hw.trans hfit.symm, hw.symm ▸ inferInstance⟩

/-- The actual natural omega action has exactly the Fitting subgroup as kernel. -/
theorem natural_action_ker_eq_fitting
    {E : Type*} [Group E] [Finite E] {C : Subgroup E}
    (hC : C.IsCComponent) (hc : A36Common C) (hn : ¬ IsQuasisimple C)
    (ha : A36Natural C) (hd : p ∣ Nat.card (fittingSubgroup C)) :
    (omegaFrattiniAction p C).ker = fittingSubgroup C := by
  obtain ⟨hw, he⟩ := natural_omega ha hd
  let := he
  let : Fact (IsPGroup p (omegaCore p C)) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  rw [action_ker_eq_centralizer (frattini_eq_bot_of_isElementaryAbelian (p := p)), hw]
  apply le_antisymm (RadicalStructure.fitting_selfCentralizing hC hc hn)
  let : IsMulCommutative (fittingSubgroup C) := hw ▸ he.toIsMulCommutative
  exact Subgroup.le_centralizer (H := fittingSubgroup C)

/-- A quaternion subgroup of the actual omega action detects the complete
Fitting kernel in the nilpotent alternative. -/
theorem nilpotent_action_ker_eq_fitting (hn : A36Nilpotent K) (hc : A36Common K)
    (hd : p ∣ Nat.card (fittingSubgroup K))
    (hQ : ∃ e : QuaternionGroup 2 →* (omegaFrattiniAction p K).range,
      Function.Injective e) :
    (omegaFrattiniAction p K).ker = fittingSubgroup K := by
  let f := omegaFrattiniAction p K
  apply le_antisymm _ (RadicalActions.Nilpotent.fitting_le_action_ker hn hd)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hn.2.2.1
  have hquot : Nat.card (K ⧸ generalizedFitting K) = 120 := by
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]
    norm_num
  have hcard : Nat.card K = 120 * Nat.card (fittingSubgroup K) := by
    rw [card_eq_card_quotient_mul_card_subgroup (generalizedFitting K), hquot, hn.1]
  have h8 : 8 ∣ Nat.card f.range := by
    obtain ⟨e, he⟩ := hQ
    simpa only [Nat.card_eq_fintype_card, QuaternionGroup.card] using card_dvd_of_injective e he
  have hmul : Nat.card f.range * Nat.card f.ker = Nat.card K := by
    rw [← index_ker]
    exact f.ker.index_mul_card
  have hcop : Nat.Coprime 2 (Nat.card (fittingSubgroup K)) := by
    rw [hc.1]
    exact pPrimeCore_coprime_card
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd2
    have h16 : 8 * 2 ∣ 8 * (15 * Nat.card (fittingSubgroup K)) := by
      have hh := Nat.mul_dvd_mul h8 hd2
      rw [hmul, hcard] at hh
      convert hh using 1
      ring
    have h2 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp h16
    exact (Nat.prime_two.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 2 15).mul_right hcop)) h2
  rw [hc.1]
  exact le_sSup ⟨inferInstance, hk⟩


/-- Actual component and Sylow actions, with one kernel for every Fitting prime.
The structural quotient models and prime restrictions remain in A36Conclusion. -/
def OmegaActionData (B : Type*) [Group B] : Prop :=
  generalizedFitting B = fittingSubgroup B ∧
    fittingSubgroup B = pPrimeCore 2 B ∧
    ∀ (r : ℕ) [Fact r.Prime], r ∣ Nat.card (fittingSubgroup B) →
      3 < r ∧ (omegaFrattiniAction r B).ker = fittingSubgroup B ∧
      (∀ A : Subgroup (omegaCore r B ⧸ frattini (omegaCore r B)),
        (∀ b : B, ∀ a ∈ A, omegaFrattiniAction r B b a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      (∀ S : Sylow 2 B,
        (∀ A : Subgroup (omegaCore r B ⧸ frattini (omegaCore r B)),
          (∀ s : S, ∀ a ∈ A, omegaFrattiniAction r B s a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
        ∃ f : QuaternionGroup 2 →*
            ((omegaFrattiniAction r B).comp (S : Subgroup B).subtype).range,
          Function.Injective f)

private theorem quaternion_in_full_image {A B : Type*} [Group A] [Group B]
    (f : A →* B) (S : Subgroup A)
    (hQ : ∃ e : QuaternionGroup 2 →* (f.comp S.subtype).range, Function.Injective e) :
    ∃ e : QuaternionGroup 2 →* f.range, Function.Injective e := by
  obtain ⟨e, he⟩ := hQ
  have hle : (f.comp S.subtype).range ≤ f.range := by
    rintro a ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  exact ⟨(inclusion hle).comp e, (inclusion_injective hle).comp he⟩

universe u

/-- Assembly from a universal nilpotent Sylow-action interface. The final
`strengthened_omega_actions` theorem below proves and supplies this interface.
Natural actions, common kernels, and whole-component irreducibility are deduced
here, and the complete original A.3.6 conclusion is retained. -/
theorem strengthened_of_nilpotent_sylow_actions
    {𝒦 : GroupClass.{u}}
    (hNilpotent : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Nilpotent C → A36Common C →
      ∀ (r : ℕ) [Fact r.Prime], Odd r → r ∣ Nat.card (fittingSubgroup C) →
      ∀ S : Sylow 2 C,
        (∀ A : Subgroup (omegaCore r C ⧸ frattini (omegaCore r C)),
          (∀ s : S, ∀ a ∈ A, omegaFrattiniAction r C s a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
        ∃ f : QuaternionGroup 2 →*
            ((omegaFrattiniAction r C).comp (S : Subgroup C).subtype).range,
          Function.Injective f)
    {E : Type u} [Group E] [Finite E]
    (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent) (h : A36Conclusion C) :
    A36Conclusion C ∧ (¬ IsQuasisimple C → OmegaActionData C) := by
  refine ⟨h, fun hn => ?_⟩
  have hr := RadicalStructure.nonsimple_radical h hn
  refine ⟨hr.elim And.left And.left, h.2.1, ?_⟩
  intro p _ hd
  have hp3 := (RadicalStructure.radical_core hr hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hs : ∀ S : Sylow 2 C,
      (∀ A : Subgroup (omegaCore p C ⧸ frattini (omegaCore p C)),
        (∀ s : S, ∀ a ∈ A, omegaFrattiniAction p C s a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      ∃ f : QuaternionGroup 2 →*
          ((omegaFrattiniAction p C).comp (S : Subgroup C).subtype).range,
        Function.Injective f := by
    intro S
    rcases hr with ha | ha
    · exact natural_sylow_actions ha hd S
    · exact hNilpotent E hE hO C hC ha h.2 p ho hd S
  let S : Sylow 2 C := Classical.arbitrary _
  refine ⟨hp3, ?_, ?_, hs⟩
  · rcases hr with ha | ha
    · exact natural_action_ker_eq_fitting hC h.2 hn ha hd
    · exact nilpotent_action_ker_eq_fitting ha h.2 hd
        (quaternion_in_full_image _ _ (hs S).2)
  · intro A hA
    exact (hs S).1 A (fun s a ha => hA s a ha)

omit [Finite K] [Fact p.Prime] in
/-- The actual quotient by F is the actual action image, when the common
kernel equality is known. Together with A.3.6 this identifies its SL₂ model. -/
noncomputable def omegaActionQuotientEquiv
    (hk : (omegaFrattiniAction p K).ker = fittingSubgroup K) :
    (K ⧸ fittingSubgroup K) ≃* (omegaFrattiniAction p K).range :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange (omegaFrattiniAction p K))

omit [Finite K] [Fact p.Prime] in
/-- This isomorphism is induced by conjugation, with the original quotient map. -/
theorem omegaActionQuotientEquiv_apply_mk
    (hk : (omegaFrattiniAction p K).ker = fittingSubgroup K) (g : K) :
    (omegaActionQuotientEquiv hk (QuotientGroup.mk' (fittingSubgroup K) g) :
      MulAut (omegaCore p K ⧸ frattini (omegaCore p K))) = omegaFrattiniAction p K g := rfl

/-- In the single-prime case the sufficient centralizer statement is containment.
This also covers extraspecial cores, where equality with the core is unnecessary. -/
theorem centralizer_omega_le_core_of_common_kernel
    (h : A36Natural K ∨ A36Nilpotent K) (hc : A36Common K)
    (hs : ∀ q : ℕ, q.Prime → Odd q → q ∣ Nat.card (fittingSubgroup K) → q = p)
    (hk : (omegaFrattiniAction p K).ker = fittingSubgroup K) :
    centralizer (omegaCore p K : Set K) ≤ pCore p K := by
  have hcore := RadicalStructure.core_eq_generalizedFitting h hc hs
  have hfit : generalizedFitting K = fittingSubgroup K := h.elim And.left And.left
  rw [hcore, hfit, ← hk]
  exact omega_centralizer_le_action_ker


/-- The full A.3.6 data imply the actual omega-action conclusions. All action
premises are proved here; the original structural assertions are retained. -/
theorem strengthened_omega_actions
    {𝒦 : GroupClass.{u}} {E : Type u} [Group E] [Finite E]
    (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent) (h : A36Conclusion C) :
    A36Conclusion C ∧ (¬ IsQuasisimple C → OmegaActionData C) := by
  apply strengthened_of_nilpotent_sylow_actions (𝒦 := 𝒦) ?_ hE hO hC h
  intro X _ _ _ _ B hB hnil _ p _ hp hd S
  let : Group.IsPerfect B := hB.perfect
  exact nilpotent_sylow_actions hnil hp hd S

/-- Universal strengthened source interface for the radical consumers. The
only earlier-source premise is the unchanged A.3.6 classification itself;
there is no extra representation or center–Frattini premise. -/
theorem strengthened_A36_of_A36
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C) :
    ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C ∧ (¬ IsQuasisimple C → OmegaActionData C) := by
  intro E _ _ hE hO C hC
  exact strengthened_omega_actions hE hO hC (hA36 E hE hO C hC)

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
