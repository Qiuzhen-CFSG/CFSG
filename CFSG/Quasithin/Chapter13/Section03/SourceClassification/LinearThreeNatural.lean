module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The original L₃(2) choice is natural once its order is eight

The Irr⁺ condition and simplicity identify the literal conjugation kernel
with O₂(L). Descend that action through L → L/O₂(L), choose binary
coordinates, and compare orders with GL₃(2). The resulting natural marking
intertwines the original quotient map and the original chosen subgroup.

Only the scalar assertion |V| = 8 remains for the earlier classification
and the 12.4.2 exclusion of the four-dimensional indecomposable. This file
does not assume a natural marking or a full-action conclusion.

Source: Aschbacher--Smith, 12.2.2(3a--b), 12.4.2, and 13.3.2(3),
printed pp.795,812,885; application to 14.3.1(1), p.990.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original L₃(2) choice needs only its order, not a separately marked
natural-module isomorphism. -/
theorem linearThree_marking_of_card (D : ChosenModule T L V)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hcard : Nat.card V = 8) :
    let := D.elementary
    Nonempty (AmbientNaturalMarking L D.normalizes 3) := by
  let := D.elementary
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hq
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eP := eF.trans (Atlas.fieldEquivPSL 3 f)
  let : IsSimpleGroup PSL(3, ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
  have hs : IsSimpleGroup (L ⧸ pCore 2 L) := eP.isSimpleGroup
  let e₀ := eP.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3))
  let ρ : Representation (ZMod 2) L (Additive V) :=
    Representation.elementaryRepresentation (setupSeedAction L V D.normalizes)
  have hker : ρ.ker = pCore 2 L := by
    rw [← D.centralizer_eq_core_of_simple hs]
    ext l
    constructor
    · intro hl
      apply mem_centralizer_iff.mpr
      intro v hv
      have he := LinearMap.congr_fun (show ρ l = 1 from hl) (Additive.ofMul ⟨v, hv⟩)
      have he' := congrArg (fun x : Additive V => (x.toMul : G)) he
      change (l : G) * v * (l : G)⁻¹ = v at he'
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hl
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (v.toMul : G) * (l : G)⁻¹ = (v.toMul : G)
      exact mul_inv_eq_iff_eq_mul.mpr
        ((mem_centralizer_iff.mp hl) v.toMul v.toMul.property).symm
  let σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive V) :=
    QuotientGroup.lift (pCore 2 L) ρ hker.ge
  have hi : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    apply bot_unique
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    apply (QuotientGroup.eq_one_iff l).mpr
    apply hker.le
    exact hq
  have hd : Module.finrank (ZMod 2) (Additive V) = 3 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at he
    exact he.symm.trans hcard
  obtain ⟨e, c, hc⟩ :=
    Representation.BinaryFullLinearRecognition.exists_natural_equiv σ hi e₀ hd
  refine ⟨⟨e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3), c, ?_⟩⟩
  intro l v
  have hh := hc (QuotientGroup.mk' (pCore 2 L) l) v
  change c (ρ l v) = _ at hh
  have he : ρ l v = Additive.ofMul ⟨(l : G) * (v.toMul : G) * (l : G)⁻¹,
      (mem_normalizer_iff.mp (D.normalizes l.property) v.toMul).mp v.toMul.property⟩ := by
    rfl
  rw [he] at hh
  simpa only [MulEquiv.trans_apply, BinaryLinear.OuterCyclic.slEquivLinear_apply] using hh

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
