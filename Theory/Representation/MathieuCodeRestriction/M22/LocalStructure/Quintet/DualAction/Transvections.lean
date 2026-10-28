module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Quotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Flag
/-!
# Full transvection action on the native M22 code quotient

The coordinate-pairing quotient duality transfers the faithful, full center
radical on cocode V6 to the full axis radical on the literal quotient code/V4.
Surjectivity of finite-dimensional inverse duality gives the entire radical,
not just containment. The quotient has dimension six and its literal axis
V9.map V4.mkQ has dimension five; a nonzero form explicitly realizes the
image as all transvections with this hyperplane axis, including the identity.

The axis is canonically dual to V6/V1. Dualizing the supplied equivariant
marking of V6/V1 and applying double-dual evaluation constructs an equivariant
linear equivalence to E. Its multiplicative form, composed with the given
cocode marking, identifies the axis with the actual K under Q-conjugation.
All conclusions are conditional only on CocodeFlag and CocodeActionData;
EarlierInputs is unnecessary for this deduction.

Source: Aschbacher--Smith, H.15.4(1--2) and H.16.3(3), printed pp.400,403,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction
open BinaryLinear BinaryTransvectionGroups

section LinearTransport
variable {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

private theorem contra_surj [FiniteDimensional (ZMod 2) X] :
    Function.Surjective (contragredient (V := X)) := by
  intro t
  let e := Module.evalEquiv (ZMod 2) X
  refine ⟨e.trans (t.symm.dualMap.trans e.symm), ?_⟩
  ext f v
  change f (e.symm (t.dualMap (e v))) = t f v
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

private theorem radical_transport (e : X ≃ₗ[ZMod 2] Y) (U : Submodule (ZMod 2) X) (t : BinaryLinear.GL X) :
    e.symm.trans (t.trans e) ∈ radical (U.map e.toLinearMap) ↔ t ∈ radical U := by
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · intro v hv
      have h := ht.1 (e v) ⟨v, hv, rfl⟩
      apply e.injective
      simpa using h
    · intro v
      have h := ht.2 (e v)
      rcases h with ⟨w, hw, he⟩
      have he' : e w = e (t v - v) := by simpa using he
      exact e.injective he' ▸ hw
  · intro ht
    refine ⟨?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      change e (t (e.symm (e v))) = e v
      rw [e.symm_apply_apply, ht.1 v hv]
    · intro v
      refine ⟨t (e.symm v) - e.symm v, ht.2 _, ?_⟩
      simp

private theorem dual_radical [FiniteDimensional (ZMod 2) X] (U : Submodule (ZMod 2) X) :
    dualGroup (radical U) = radical U.dualAnnihilator := by
  ext t
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (contragredient_mem_radical_iff U g).mpr hg
  · intro ht
    obtain ⟨g, rfl⟩ := contra_surj t
    exact ⟨g, (contragredient_mem_radical_iff U g).mp ht, rfl⟩

private theorem dual_marking_ext (e : X ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Y)
    {v w : Y} (h : ∀ x, e x v = e x w) : v = w := by
  apply Module.eval_apply_injective (ZMod 2)
  ext f
  obtain ⟨x, rfl⟩ := e.surjective f
  exact h x

end LinearTransport

/-- The actual K-action on code/V4 becomes the inverse-dual cocode action. -/
theorem codeQuotientKernelAction_duality (k : K) :
    quotientDuality.symm.trans ((codeQuotientKernelAction k).trans quotientDuality) =
      contragredient (cocodeKernelAction k) := by
  ext f v
  have h := LinearMap.congr_fun
    (quotientDuality_equivariant (kernelInclusion k) (quotientDuality.symm f)) v
  change quotientDuality (codeQuotientKernelAction k (quotientDuality.symm f)) v =
    quotientDuality (quotientDuality.symm f)
      (V6Subrepresentation.toRepresentation ((kernelInclusion k)⁻¹) v) at h
  refine h.trans ?_
  rw [quotientDuality.apply_symm_apply f]
  rfl

namespace CocodeActionData
variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The literal quotient action is faithful, by faithfulness of inverse duality. -/
theorem codeQuotientKernelAction_faithful (D : CocodeActionData F E) :
    Function.Injective codeQuotientKernelAction := by
  intro k l h
  apply D.centerAction_faithful
  apply contragredient_injective
  rw [← codeQuotientKernelAction_duality, ← codeQuotientKernelAction_duality, h]

/-- The actual K-image is the entire radical of the literal code axis. -/
theorem codeQuotientKernelAction_full (D : CocodeActionData F E) :
    codeQuotientKernelAction.range = radical codeAxis := by
  let W : Submodule (ZMod 2) V6 := V1.comap V6.subtype
  have ha : codeAxis.map quotientDuality.toLinearMap = W.dualAnnihilator :=
    quotientDuality_axis F
  have hc : cocodeKernelAction.range = radical W := D.centerAction_full
  ext t
  rw [← radical_transport quotientDuality codeAxis t, ha, ← dual_radical W, ← hc]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨cocodeKernelAction k, ⟨k, rfl⟩, (codeQuotientKernelAction_duality k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, hk⟩
    refine ⟨k, ?_⟩
    rw [← codeQuotientKernelAction_duality] at hk
    ext v
    apply quotientDuality.injective
    simpa using LinearEquiv.congr_fun hk (quotientDuality v)

end CocodeActionData

namespace CocodeFlag

/-- The image V9/V4 is stable under the actual quotient representation. -/
def codeAxisSubrepresentation (F : CocodeFlag) :
    Subrepresentation V4Subrepresentation.quotientRepresentation where
  toSubmodule := codeAxis
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨codeAction g v, ?_, rfl⟩
    have h := F.codeNine.apply_mem_toSubmodule g
    rw [F.codeNine_space] at h
    exact h hv

/-- Restriction of the actual code quotient action to its invariant axis. -/
abbrev codeAxisAction (F : CocodeFlag) : Representation (ZMod 2) Q codeAxis :=
  F.codeAxisSubrepresentation.toRepresentation

/-- The induced action is literally the restriction of the code quotient action. -/
@[simp] theorem codeAxisAction_apply (F : CocodeFlag) (g : Q) (w : codeAxis) :
    (F.codeAxisAction g w).val = V4Subrepresentation.quotientRepresentation g w.val := rfl

/-- The native quotient is six-dimensional. -/
theorem codeQuotient_dim (F : CocodeFlag) :
    Module.finrank (ZMod 2) (M22Code ⧸ V4) = 6 := by
  rw [quotientDuality.finrank_eq, Subspace.dual_finrank_eq, F.dim6]

/-- The restricted coordinate pairing identifies the axis with the dual of V6/V1. -/
def axisDuality (F : CocodeFlag) :
    codeAxis ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (V6 ⧸ F.center.toSubmodule) :=
  (quotientDuality.ofSubmodules codeAxis
    (show Submodule (ZMod 2) (Module.Dual (ZMod 2) V6) from
      F.center.toSubmodule.dualAnnihilator) (quotientDuality_axis F)).trans
    (show Submodule (ZMod 2) V6 from F.center.toSubmodule).dualQuotEquivDualAnnihilator.symm

/-- Evaluation on a quotient representative is the original coordinate pairing. -/
@[simp] theorem axisDuality_mk (F : CocodeFlag) (w : codeAxis) (v : V6) :
    F.axisDuality w (F.center.toSubmodule.mkQ v) = quotientDuality w.val v := rfl

end CocodeFlag

namespace CocodeActionData
variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The axis marking obtained by dualizing middleEquiv and evaluating the double dual. -/
def codeAxisEquiv (D : CocodeActionData F E) : codeAxis ≃ₗ[ZMod 2] E :=
  ((F.axisDuality.trans D.middleEquiv.symm.dualMap).trans
    (Module.evalEquiv (ZMod 2) E).symm)

/-- The axis marking preserves the dual pairing with the cocode middle section. -/
theorem codeAxisEquiv_pair (D : CocodeActionData F E) (w : codeAxis)
    (v : V6 ⧸ F.center.toSubmodule) :
    D.middleEquiv v (D.codeAxisEquiv w) = F.axisDuality w v := by
  change D.middleEquiv v ((Module.evalEquiv (ZMod 2) E).symm
    (D.middleEquiv.symm.dualMap (F.axisDuality w))) = _
  calc
    _ = D.middleEquiv.symm.dualMap (F.axisDuality w) (D.middleEquiv v) :=
      Module.apply_evalEquiv_symm_apply (ZMod 2) E (D.middleEquiv v) _
    _ = F.axisDuality w v := congrArg (F.axisDuality w) (D.middleEquiv.symm_apply_apply v)

/-- The axis marking preserves the coordinate pairing on representatives. -/
theorem codeAxisEquiv_pair_mk (D : CocodeActionData F E) (w : codeAxis) (v : V6) :
    D.middleEquiv (F.center.toSubmodule.mkQ v) (D.codeAxisEquiv w) =
      quotientDuality w.val v :=
  (D.codeAxisEquiv_pair w (F.center.toSubmodule.mkQ v)).trans (F.axisDuality_mk w v)

/-- The constructed linear equivalence intertwines the actual Q-action with kernelAction. -/
theorem codeAxisEquiv_equivariant (D : CocodeActionData F E) (g : Q) (w : codeAxis) :
    D.codeAxisEquiv (F.codeAxisAction g w) = D.kernelAction g (D.codeAxisEquiv w) := by
  apply dual_marking_ext D.middleEquiv
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have h : D.middleEquiv (F.center.toSubmodule.mkQ v)
        (D.kernelAction g (D.codeAxisEquiv w)) =
        quotientDuality w.val (V6Subrepresentation.toRepresentation g⁻¹ v) := by
      calc
        _ = D.kernelAction.dual g⁻¹ (D.middleEquiv (F.center.toSubmodule.mkQ v))
            (D.codeAxisEquiv w) := by
          change _ = D.middleEquiv (F.center.toSubmodule.mkQ v)
            (D.kernelAction ((g⁻¹)⁻¹) (D.codeAxisEquiv w))
          exact congrArg (fun a : Q => D.middleEquiv (F.center.toSubmodule.mkQ v)
            (D.kernelAction a (D.codeAxisEquiv w))) (inv_inv g).symm
        _ = D.middleEquiv (F.middleAction g⁻¹ (F.center.toSubmodule.mkQ v))
            (D.codeAxisEquiv w) :=
          congrArg (fun f : Module.Dual (ZMod 2) E => f (D.codeAxisEquiv w))
            (D.middleEquiv_equivariant g⁻¹ (F.center.toSubmodule.mkQ v)).symm
        _ = _ := D.codeAxisEquiv_pair_mk w (V6Subrepresentation.toRepresentation g⁻¹ v)
    exact (D.codeAxisEquiv_pair_mk (F.codeAxisAction g w) v).trans
      ((LinearMap.congr_fun (quotientDuality_equivariant g w.val) v).trans h.symm)

/-- The literal axis is five-dimensional. -/
theorem codeAxis_dim (D : CocodeActionData F E) :
    Module.finrank (ZMod 2) codeAxis = 5 :=
  D.codeAxisEquiv.finrank_eq.trans D.kernel_dim

/-- The literal axis is a hyperplane in the six-dimensional quotient. -/
theorem codeAxis_codimension (D : CocodeActionData F E) :
    Module.finrank (ZMod 2) ((M22Code ⧸ V4) ⧸ codeAxis) = 1 := by
  have h := codeAxis.finrank_quotient_add_finrank
  rw [D.codeAxis_dim, F.codeQuotient_dim] at h
  omega

/-- A nonzero linear form cuts out exactly the literal code axis. -/
theorem exists_codeAxis_form (D : CocodeActionData F E) :
    ∃ f : Module.Dual (ZMod 2) (M22Code ⧸ V4), f ≠ 0 ∧ f.ker = codeAxis := by
  have hproper : codeAxis < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    have hd := D.codeAxis_dim
    rw [h, finrank_top, F.codeQuotient_dim] at hd
    omega
  obtain ⟨f, hf, hle⟩ := codeAxis.exists_le_ker_of_lt_top hproper
  refine ⟨f, hf, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [F.codeQuotient_dim] at h
  rw [D.codeAxis_dim]
  omega

/-- Every rank-one transvection with this axis occurs in the K-image, and conversely.
The zero direction gives the identity, as required for a group. -/
theorem codeQuotient_transvections (D : CocodeActionData F E) :
    ∃ f : Module.Dual (ZMod 2) (M22Code ⧸ V4), f ≠ 0 ∧ f.ker = codeAxis ∧
      ∀ t : BinaryLinear.GL (M22Code ⧸ V4),
        t ∈ codeQuotientKernelAction.range ↔
          ∃ w, ∃ hw : f w = 0, t = BinaryLinear.transvection w f hw := by
  obtain ⟨f, hf, haxis⟩ := D.exists_codeAxis_form
  refine ⟨f, hf, haxis, fun t => ?_⟩
  have h := mem_axisRootGroup_iff (G := (⊤ : Subgroup (BinaryLinear.GL (M22Code ⧸ V4))))
    hf (t := t)
  simpa only [axisRootGroup, top_inf_eq, Subgroup.mem_top, true_and,
    haxis, D.codeQuotientKernelAction_full] using h

/-- An actual group isomorphism from the additive code axis to K. -/
def codeAxisMarking (D : CocodeActionData F E) : Multiplicative codeAxis ≃* K :=
  (AddEquiv.toMultiplicative D.codeAxisEquiv.toAddEquiv).trans D.kernelMarking

/-- The group marking is the multiplicative form of the constructed linear marking. -/
@[simp] theorem codeAxisMarking_apply (D : CocodeActionData F E) (w : codeAxis) :
    D.codeAxisMarking (Multiplicative.ofAdd w) =
      D.kernelMarking (Multiplicative.ofAdd (D.codeAxisEquiv w)) := rfl

/-- The axis group marking intertwines the native Q-action with ambient conjugation. -/
theorem codeAxisMarking_equivariant (D : CocodeActionData F E) (g : Q) (w : codeAxis) :
    (D.codeAxisMarking (Multiplicative.ofAdd (F.codeAxisAction g w))).val =
      g.val * (D.codeAxisMarking (Multiplicative.ofAdd w)).val * g.val⁻¹ := by
  change (D.kernelMarking (Multiplicative.ofAdd (D.codeAxisEquiv (F.codeAxisAction g w)))).val = _
  rw [D.codeAxisEquiv_equivariant]
  exact D.kernelMarking_equivariant g (D.codeAxisEquiv w)

end CocodeActionData
end MathieuCode.M22Quintet.DualAction
