module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Coordinates
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Recognition
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Collection
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Centralizer

/-!
# Parker triality normal forms

Every element of the concrete centralizer `N1 = C_N(z1N)` has a unique word
`psiAut1N α * psi2N e * psi1N d`. This reverses the source right-action word
`ψ₁(d)ψ₂(e)ψ₁(α)` for Lean's left composition. The word lies in `Q1` exactly
when `e.code = 0` and the standard automorphism induces the identity on the
Golay code, and lies in `NPlus` exactly when that automorphism fixes
`parkerOmega`.

Collection in the actual centralizer supplies existence; the three-axis action
supplies uniqueness. The generator relation proving `z2N ∈ Q1` discharges the
remaining premise of recognition, giving an actual `Q1` word equivalence and
order `2^26`. The first-code action gives relative normality in `N1`, and the
four-group's action gives `Q1 ⊓ K = K1`. Normality of `K` and the action on
`K1`-orbits then identify the centralizer preimage as `K ⊔ ⟨z1N⟩`.

Source: Aschbacher, *Sporadic Groups*, Section 14, especially Lemmas 14.2–14.4,
printed pp. 58–62. The quotient by `K` is essential in Lemma 14.4(2).
No extraspeciality assertion is made for unquotiented `Q1`.
-/

public section
open Atlas.Fischer Atlas.Codes
open scoped commutatorElement
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

/-- Aschbacher 14.4(4): existence and uniqueness of the actual normal-form word. -/
theorem normalForm_bijective : Function.Bijective
    (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup =>
      normalForm x.1 x.2.1 x.2.2) :=
  ⟨normalForm_injective, normalForm_surjective⟩

/-- The normal-form coordinates on the concrete centralizer, before quotienting. -/
@[expose] def normalFormEquiv : (ParkerLoop × ParkerLoop × ParkerStandardGroup) ≃ N1 :=
  Equiv.ofBijective _ normalForm_bijective

@[simp] theorem normalFormEquiv_apply (d e : ParkerLoop) (α : ParkerStandardGroup) :
    normalFormEquiv (d, e, α) = normalForm d e α := rfl

/-- The exact `Q1` parameter restriction in Aschbacher 14.4(4). -/
theorem normalForm_mem_Q1_iff (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (normalForm d e α).val ∈ Q1 ↔ e.1 = 0 ∧ parkerStandardProjection α = 1 :=
  normalForm_mem_Q1_iff_of_z2 z2N_mem_Q1 d e α

/-- In the centralizer, `Q1` is the kernel of the first-coordinate code action. -/
theorem mem_Q1_iff_firstCode (g : N) (hg : g ∈ N1) :
    g ∈ Q1 ↔ ∀ x, firstCode (g.val x) = firstCode x :=
  mem_Q1_iff_firstCode_of_collection normalForm_surjective z2N_mem_Q1 g hg

/-- Aschbacher 14.4(1), with normality relative to the source overgroup `N1`. -/
theorem Q1_normal_in_N1 : (Q1.subgroupOf N1).Normal :=
  Q1_normal_in_N1_of_collection normalForm_surjective z2N_mem_Q1

theorem q1Word_mem_Q1 (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    (q1Word d t c).val ∈ Q1 :=
  q1Word_mem_Q1_of_z2 z2N_mem_Q1 d t c

/-- The specialized source word as an element of `Q1`. -/
@[expose] def q1Param (x : ParkerLoop × ParkerBit × Cocode) : Q1 :=
  q1ParamOfZ2 z2N_mem_Q1 x

@[simp] theorem q1Param_val (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    (q1Param (d, t, c)).val = (q1Word d t c).val := rfl

theorem q1Param_bijective : Function.Bijective q1Param :=
  ⟨q1ParamOfZ2_injective z2N_mem_Q1,
    q1ParamOfZ2_surjective normalForm_surjective z2N_mem_Q1⟩

/-- A bijective parametrization by the actual `q1Word` map. -/
@[expose] def q1WordEquiv : (ParkerLoop × ParkerBit × Cocode) ≃ Q1 :=
  Equiv.ofBijective q1Param q1Param_bijective

@[simp] theorem q1WordEquiv_apply (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    (q1WordEquiv (d, t, c)).val = (q1Word d t c).val := rfl

/-- The unquotiented subgroup has `2^13 · 2 · 2^12` elements. -/
theorem Q1_card : Nat.card Q1 = 2 ^ 26 :=
  Q1_card_of_collection normalForm_surjective z2N_mem_Q1

theorem K1_le_Q1 : K1 ≤ Q1 := K1_le_Q1_of_z2 z2N_mem_Q1

/-- Aschbacher 14.4(5), in the concrete group before quotienting by `K`. -/
theorem Q1_inf_K_eq_K1 : Q1 ⊓ K = K1 := Q1_inf_K_eq_K1_of_z2 z2N_mem_Q1

/-- The preimage form of the centralizer clause of Aschbacher 14.4(2).
Commutation is modulo `K`, and the element belongs to the actual `N1`. -/
theorem centralizer_preimage (g : N) (hg : g ∈ N1) :
    (∀ q : N, q ∈ Q1 → ⁅g,q⁆ ∈ K) ↔ g ∈ K ⊔ Subgroup.zpowers z1N :=
  centralizer_preimage_of_collection normalForm_surjective z2N_mem_Q1 g hg

end Sporadic.Monster.Construction.TrialitySpin
