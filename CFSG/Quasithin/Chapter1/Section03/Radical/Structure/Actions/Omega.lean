module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# The radical omega actions and their actual coordinates

The characteristic subgroup Ω₁(Oₚ(K)) has its intrinsic conjugation action.
Isomorphisms of K preserve that subgroup and its Frattini quotient, including
all action formulas. The quotient of Ξₚ(L) is compared with this omega core
using the original two-core quotient map, so conjugation by L corresponds to
conjugation by L/O₂(L). Higher homocyclic exponents are retained throughout.

For the natural alternative, SL₂ transitivity on nonzero vectors also proves
irreducibility under the whole component. Its restriction to a Sylow two-group,
and the nilpotent alternative's action, remain separate model obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 on
pp.43–45, the definition before 1.3.3 on p.509, and the actions used on
pp.513–514. The natural action calculation uses `Matrix.SL2.naturalAction_irreducible`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {K : Type*} [Group K]
/-- The first omega subgroup of the odd core, embedded in the component. -/
def omegaCore (p : ℕ) (K : Type*) [Group K] : Subgroup K :=
  (omega (pCore p K) (p := p) 1).map (pCore p K).subtype
instance omegaCore_characteristic (p : ℕ) : (omegaCore p K).Characteristic := by
  let := omega_characteristic (pCore p K) (p := p) 1
  exact Subgroup.characteristic_of_characteristic_of_characteristic
/-- Actual component conjugation on its omega core. -/
def omegaCoreAction (p : ℕ) (K : Type*) [Group K] : K →* MulAut (omegaCore p K) :=
  (MulAut.characteristic (omegaCore p K)).comp (MulAut.conj)
/-- Actual component conjugation on the Frattini quotient of its omega core. -/
def omegaFrattiniAction (p : ℕ) (K : Type*) [Group K] :
    K →* MulAut ((omegaCore p K) ⧸ frattini (omegaCore p K)) :=
  (quotientAut (frattini (omegaCore p K))).comp (omegaCoreAction p K)
theorem omegaCoreAction_apply (p : ℕ) (g : K) (x : omegaCore p K) :
    ((omegaCoreAction p K g x : omegaCore p K) : K) = g * x * g⁻¹ := rfl

theorem natural_irreducible [Finite K] {N : Subgroup K} [N.Normal] {p : ℕ}
    (h : LocalModels.NaturalSL2Action K N p) :
    ∀ A : Subgroup N,
      (∀ (g : K) (x : N), x ∈ A →
        (⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ : N) ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  obtain ⟨F, _, _, _, v, ρ, ha⟩ := h
  intro A hA
  have hi : ∀ g x, x ∈ A.map v.toMonoidHom →
      Matrix.SL2.naturalAction F g x ∈ A.map v.toMonoidHom := by
    intro g x hx
    obtain ⟨a, haA, rfl⟩ := hx
    obtain ⟨b, hb⟩ := ρ.surjective g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N b
    refine ⟨⟨k * a * k⁻¹, (inferInstance : N.Normal).conj_mem a a.property k⟩,
      hA k a haA, ?_⟩
    change v _ = Matrix.SL2.naturalAction F g (v a)
    rw [ha, hb]
    rfl
  rcases Matrix.SL2.naturalAction_irreducible F (A.map v.toMonoidHom) hi with hb | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective v.injective).mp hb)
  · right
    apply map_injective (f := v.toMonoidHom) v.injective
    rw [map_top_of_surjective v.toMonoidHom v.surjective]
    exact ht

/-- Isomorphisms preserve the embedded omega core. -/
theorem omegaCore_map {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) : (omegaCore p A).map e.toMonoidHom = omegaCore p B := by
  let eC := (e.subgroupMap (pCore p A)).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  have he : e.toMonoidHom.comp (pCore p A).subtype =
      (pCore p B).subtype.comp eC.toMonoidHom := rfl
  unfold omegaCore
  rw [map_map, he, ← map_map, eC.map_omega p 1]

/-- Coordinate transport on the actual embedded omega core. -/
noncomputable def omegaCoreEquiv {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) : omegaCore p A ≃* omegaCore p B :=
  (e.subgroupMap (omegaCore p A)).trans (MulEquiv.subgroupCongr (omegaCore_map p e))

theorem omegaCoreEquiv_apply {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) (x : omegaCore p A) :
    ((omegaCoreEquiv p e x : omegaCore p B) : B) = e x := rfl

/-- The transported omega coordinates preserve conjugation. -/
theorem omegaCoreEquiv_equivariant {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) (g : A) (x : omegaCore p A) :
    omegaCoreEquiv p e (omegaCoreAction p A g x) =
      omegaCoreAction p B (e g) (omegaCoreEquiv p e x) := by
  apply Subtype.ext
  simp only [omegaCoreEquiv_apply, omegaCoreAction_apply, map_mul, map_inv]

private theorem frattini_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    exact ⟨e.symm b, frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb, e.apply_symm_apply b⟩

/-- The same coordinates on the Frattini quotient of the omega core. -/
noncomputable def omegaFrattiniEquiv {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) :
    (omegaCore p A ⧸ frattini (omegaCore p A)) ≃*
      (omegaCore p B ⧸ frattini (omegaCore p B)) :=
  QuotientGroup.congr _ _ (omegaCoreEquiv p e) (by exact frattini_map_equiv _)

theorem omegaFrattiniEquiv_apply_mk {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) (x : omegaCore p A) :
    omegaFrattiniEquiv p e (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (omegaCoreEquiv p e x) := rfl

/-- Quotienting the transported core coordinates still intertwines conjugation. -/
theorem omegaFrattiniEquiv_equivariant {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) (g : A) (x : omegaCore p A ⧸ frattini (omegaCore p A)) :
    omegaFrattiniEquiv p e (omegaFrattiniAction p A g x) =
      omegaFrattiniAction p B (e g) (omegaFrattiniEquiv p e x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    change omegaFrattiniEquiv p e (omegaFrattiniAction p A g (QuotientGroup.mk' _ x)) =
      omegaFrattiniAction p B (e g) (omegaFrattiniEquiv p e (QuotientGroup.mk' _ x))
    simp only [omegaFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
      omegaFrattiniEquiv_apply_mk, omegaCoreEquiv_equivariant]

/-- The actual radical quotient, with its omega core embedded in L/O₂(L). -/
noncomputable def xiPQuotientEquivCore [Finite K] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup K) : XiQuotient (XiP p L₀) ≃* omegaCore p (XiQuotient L₀) :=
  let e : xiPIn p L₀ ≃* XiP p L₀ :=
    (xiPIn p L₀).equivMapOfInjective L₀.subtype L₀.subtype_injective
  (QuotientGroup.congr (pCore 2 (XiP p L₀)) (pCore 2 (xiPIn p L₀)) e.symm
    (pCore_map_iso 2 e.symm)).trans (xiPInQuotientEquivOmega ho L₀)

theorem xiPQuotientEquivCore_apply_mk [Finite K] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup K) (x : XiP p L₀) :
    ((xiPQuotientEquivCore ho L₀ (QuotientGroup.mk' _ x) : omegaCore p (XiQuotient L₀)) :
      XiQuotient L₀) = QuotientGroup.mk' _ (inclusion (XiP_le p L₀) x) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := hx
  let e : xiPIn p L₀ ≃* XiP p L₀ :=
    (xiPIn p L₀).equivMapOfInjective L₀.subtype L₀.subtype_injective
  change ((xiPInQuotientEquivOmega ho L₀
    ((QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm))
      (QuotientGroup.mk' _ (e ⟨a, ha⟩))) : xiOmegaCore p L₀) : XiQuotient L₀) = _
  change ((xiPInQuotientEquivOmega ho L₀ (QuotientGroup.mk' _ (e.symm (e ⟨a, ha⟩))) :
    xiOmegaCore p L₀) : XiQuotient L₀) = _
  rw [e.symm_apply_apply]
  rfl

/-- The actual isomorphism on the iterated radical Frattini quotient. -/
noncomputable def xiPFrattiniEquivCore [Finite K] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup K) :
    XiFrattiniQuotient (XiP p L₀) ≃*
      (omegaCore p (XiQuotient L₀) ⧸ frattini (omegaCore p (XiQuotient L₀))) :=
  QuotientGroup.congr _ _ (xiPQuotientEquivCore ho L₀) (by exact frattini_map_equiv _)

theorem xiPFrattiniEquivCore_apply_mk [Finite K] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup K) (x : XiQuotient (XiP p L₀)) :
    xiPFrattiniEquivCore ho L₀ (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (xiPQuotientEquivCore ho L₀ x) := rfl

/-- The radical Frattini isomorphism intertwines L-conjugation with the actual
omega action of its quotient. -/
theorem xiPFrattiniEquivCore_equivariant [Finite K] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup K) (g : L₀) (x : XiFrattiniQuotient (XiP p L₀)) :
    xiPFrattiniEquivCore ho L₀
      (xiFrattiniAction L₀ (XiP p L₀) (XiP_invariant p L₀.le_normalizer) g x) =
    omegaFrattiniAction p (XiQuotient L₀) (QuotientGroup.mk' _ g)
      (xiPFrattiniEquivCore ho L₀ x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x =>
      change xiPFrattiniEquivCore ho L₀
        (xiFrattiniAction L₀ (XiP p L₀) _ g
          (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
        omegaFrattiniAction p (XiQuotient L₀) (QuotientGroup.mk' _ g)
          (xiPFrattiniEquivCore ho L₀ (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
        xiPFrattiniEquivCore_apply_mk, omegaFrattiniAction]
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      simp only [xiPQuotientEquivCore_apply_mk, omegaCoreAction_apply, ← map_mul, ← map_inv]
      rfl

end CFSG.Quasithin.Chapter1.RadicalActions
