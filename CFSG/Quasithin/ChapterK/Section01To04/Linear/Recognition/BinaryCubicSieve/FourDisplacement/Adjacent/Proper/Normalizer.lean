module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Contracts
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryOffender.NormalizerImage
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Excluding graph actors from separated proper adjacent supports

The checked automorphism theorem writes each automorphism of binary SL₄ as
inner or inner times the positive-root-preserving diagram reversal. An actual
normalizer operator in the second case gives a nonzero highest vector with
reversed support on the same module. Thus separation of the two proper
supports forces its conjugation action to be inner. For an involution,
binary Schur's lemma removes the remaining centralizing operator.

The support-separation premise is still an independent representation-theoretic
obligation. The conclusion applies to every elementary actor in the entire
linear normalizer and is consumed by `Adjacent.Proper`.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28; Aschbacher–Smith K.3.2, pp.454–455.
-/

public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Proper

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def imageEquiv (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) : Group ≃* actionImage σ :=
  MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))

/-- Conjugation on the marked SL₄ action image. -/
noncomputable def conjugation (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) : linearNormalizer σ →* MulAut Group :=
  (MulAut.congr (imageEquiv σ hf).symm).toMonoidHom.comp
    (actionImage σ).normalizerMonoidHom

theorem conjugation_apply (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (t : linearNormalizer σ) (g : Group) :
    σ.asGroupHom (conjugation σ hf t g) =
      t.val * σ.asGroupHom g * t.val⁻¹ := by
  let e := imageEquiv σ hf
  change (e (e.symm ((actionImage σ).normalizerMonoidHom t (e g)))).val = _
  rw [e.apply_symm_apply]
  rfl

private theorem inner_diagram (a : MulAut Group) :
    ∃ g : Group, a = MulAut.conj g ∨ a = MulAut.conj g * diagramReversal := by
  let e := slEquivLinear 4
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inl rfl) (MulAut.congr e a)
  · refine ⟨e.symm g, Or.inl ?_⟩
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hg
  · have ha : a = graphSL 4 * MulAut.conj (e.symm g) := by
      apply (MulAut.congr e).injective
      rw [map_mul, MulAut.congr_conj, e.apply_symm_apply]
      exact hg
    refine ⟨graphSL 4 (e.symm g) * longestExchange⁻¹, Or.inr ?_⟩
    rw [ha]
    ext x : 1
    change graphSL 4 (e.symm g * x * (e.symm g)⁻¹) =
      (graphSL 4 (e.symm g) * longestExchange⁻¹) *
        (longestExchange * graphSL 4 x * longestExchange⁻¹) *
          (graphSL 4 (e.symm g) * longestExchange⁻¹)⁻¹
    rw [map_mul, map_mul, map_inv]
    group

private theorem highest_map
    {σ τ : Representation (ZMod 2) Group V} (f : V →ₗ[ZMod 2] V)
    (he : ∀ g x, σ g (f x) = f (τ g x))
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector τ J v) :
    LocalHighestVector σ J (f v) := by
  constructor
  · intro i j hij
    rw [he, h.upper_fixed i j hij]
  · intro i hi
    rw [he, h.inactive_fixed i hi]
  · intro i hi
    rw [he, he, ← map_add, ← map_add, h.active_relation i hi, map_zero]

/-- An operator implementing diagram reversal produces a nonzero highest
vector with the opposite adjacent support on the original space. -/
theorem opposite_support_of_diagram_operator
    (σ : Representation (ZMod 2) Group V) (d : (Module.End (ZMod 2) V)ˣ)
    (hd : ∀ g, σ.asGroupHom (diagramReversal g) = d * σ.asGroupHom g * d⁻¹)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v) :
    ∃ w : V, w ≠ 0 ∧ LocalHighestVector σ {1, 2} w := by
  have he (g : Group) (x : V) :
      σ g ((d⁻¹).val x) = (d⁻¹).val (diagramTwist σ g x) := by
    have hm : σ.asGroupHom g * d⁻¹ = d⁻¹ * σ.asGroupHom (diagramReversal g) := by
      rw [hd]
      group
    exact congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val x) hm
  have hne : (d⁻¹).val v ≠ 0 := by
    intro hz
    apply hv
    have hh := congrArg (fun x => d.val x) hz
    simpa only [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply, map_zero] using hh
  refine ⟨(d⁻¹).val v, hne, ?_⟩
  have htw := localHighestVector_diagramTwist h
  have hj : ({0, 1} : Finset (Fin 3)).image Fin.rev = {1, 2} := by decide
  rw [hj] at htw
  exact highest_map (d⁻¹).val he htw

/-- Support separation eliminates graph automorphisms induced by actual
normalizer operators. It does not assume that every automorphism is inner. -/
theorem conjugation_inner_of_support_separation
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hsep : ProperSupportSeparation σ) {v : V} (hv : v ≠ 0)
    (h : LocalHighestVector σ {0, 1} v) (t : linearNormalizer σ) :
    conjugation σ hf t ∈ MulAut.innerSubgroup Group := by
  obtain ⟨g, hg | hg⟩ := inner_diagram (conjugation σ hf t)
  · exact ⟨g, hg.symm⟩
  · let d : (Module.End (ZMod 2) V)ˣ := (σ.asGroupHom g)⁻¹ * t.val
    have hd (x : Group) :
        σ.asGroupHom (diagramReversal x) = d * σ.asGroupHom x * d⁻¹ := by
      have hc := conjugation_apply σ hf t x
      rw [hg] at hc
      change σ.asGroupHom (g * diagramReversal x * g⁻¹) = _ at hc
      rw [map_mul, map_mul, map_inv] at hc
      calc
        _ = (σ.asGroupHom g)⁻¹ *
            (σ.asGroupHom g * σ.asGroupHom (diagramReversal x) * (σ.asGroupHom g)⁻¹) *
              σ.asGroupHom g := by group
        _ = (σ.asGroupHom g)⁻¹ *
            (t.val * σ.asGroupHom x * t.val⁻¹) * σ.asGroupHom g := by rw [hc]
        _ = _ := by dsimp [d]; group
    obtain ⟨w, hw, hW⟩ := opposite_support_of_diagram_operator σ d hd hv h
    exact (hsep v hv h w hw hW).elim

/-- Binary Schur's lemma removes the centralizing ambiguity of an involution
whose induced automorphism is inner. -/
theorem involution_mem_image_of_inner
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hin : conjugation σ hf t ∈ MulAut.innerSubgroup Group) :
    t.val ∈ actionImage σ := by
  obtain ⟨g, hg⟩ := hin
  let e := imageEquiv σ hf
  let : Finite (actionImage σ) := Finite.of_surjective e e.surjective
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp
      (actionImage σ).subtype) := imageRepresentation_isIrreducible σ hi
  apply involution_mem_of_inner (Units.coeHom (Module.End (ZMod 2) V)) (actionImage σ)
    (fun _ _ he => Units.ext he) t (congrArg Subtype.val ht)
  refine ⟨e g, ?_⟩
  apply (MulAut.congr e.symm).injective
  rw [MulAut.congr_conj, e.symm_apply_apply]
  exact hg.symm

/-- Once the two proper supports are separated, every elementary actor lies
in the literal component image, even in the full linear normalizer. -/
theorem elementary_le_image_of_support_separation
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (hsep : ProperSupportSeparation σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) := by
  let : IsElementaryAbelian 2 A := hA.2
  intro t ht
  exact involution_mem_image_of_inner σ hf hi t
    (elemPow_eq_one_of_isElementaryAbelian t ht)
    (conjugation_inner_of_support_separation σ hf hsep hv h t)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Proper
