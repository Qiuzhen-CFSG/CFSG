module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors.Parity

/-!
# The actor centralizer in the order-168 normalizer

An automorphism of the binary four-space commuting with a = (01)(23)
is determined by the images of the zeroth and second coordinate vectors.
When it preserves parity, a finite calculation gives fourth power one.
For the actual normalizer the action kernel is E, of exponent two; hence
every element centralizing a has eighth power one.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
namespace L27NormalizerActors

private def basis (i : Fin 4) : BinaryFour := Multiplicative.ofAdd (Pi.single i 1)

private def mat (u v : BinaryFour) (x : BinaryFour) : BinaryFour :=
  u ^ (x.toAdd 0).val * (twistedAction a.right u) ^ (x.toAdd 1).val *
  v ^ (x.toAdd 2).val * (twistedAction a.right v) ^ (x.toAdd 3).val

private theorem basis_expansion : ∀ x : BinaryFour,
    x = basis 0 ^ (x.toAdd 0).val * basis 1 ^ (x.toAdd 1).val *
      basis 2 ^ (x.toAdd 2).val * basis 3 ^ (x.toAdd 3).val := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mat_fourth : ∀ u v : BinaryFour, parity u = 1 → parity v = 1 →
    (∀ x : BinaryFour, mat u v x = 1 → x = 1) →
    ∀ x : BinaryFour, mat u v (mat u v (mat u v (mat u v x))) = x := by
  decide +kernel

/-- The parity-preserving binary centralizer of a has exponent dividing four. -/
public theorem centralizing_a_fourth (f : MulAut BinaryFour)
    (hp : ∀ v, parity (f v) = parity v)
    (hc : f * twistedAction a.right = twistedAction a.right * f) : f ^ 4 = 1 := by
  have hc' (v : BinaryFour) : f (twistedAction a.right v) = twistedAction a.right (f v) :=
    congrArg (fun g : MulAut BinaryFour => g v) hc
  have h1 : twistedAction a.right (basis 0) = basis 1 := by decide +kernel
  have h3 : twistedAction a.right (basis 2) = basis 3 := by decide +kernel
  have hf (x : BinaryFour) : f x = mat (f (basis 0)) (f (basis 2)) x := by
    calc
      f x = f (basis 0 ^ (x.toAdd 0).val * basis 1 ^ (x.toAdd 1).val *
          basis 2 ^ (x.toAdd 2).val * basis 3 ^ (x.toAdd 3).val) :=
        congrArg f (basis_expansion x)
      _ = _ := by
        simp only [map_mul, map_pow, ← h1, ← h3, hc']
        rfl
  have hfour := mat_fourth (f (basis 0)) (f (basis 2))
    ((hp _).trans (by decide +kernel)) ((hp _).trans (by decide +kernel))
    (fun x hx => f.injective ((hf x).trans (hx.trans f.map_one.symm)))
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  rw [hf (f (f (f x))), hf (f (f x)), hf (f x), hf x]
  exact hfour x

end L27NormalizerActors

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The coordinate action has precisely the actual elementary subgroup as kernel. -/
public theorem eNormalizerBinaryAction_ker :
    (eNormalizerBinaryAction D k).ker =
      (E D k).subgroupOf (normalizer (E D k : Set G)) := by
  have he : (eNormalizerBinaryAction D k).ker = (E D k).normalizerMonoidHom.ker := by
    ext n
    change MulAut.congr (eBinaryEquiv D k).symm ((E D k).normalizerMonoidHom n) = 1 ↔
      (E D k).normalizerMonoidHom n = 1
    rw [← (MulAut.congr (eBinaryEquiv D k).symm).map_one,
      (MulAut.congr (eBinaryEquiv D k).symm).injective.eq_iff]
  rw [he, normalizerMonoidHom_ker, E_centralizer]

/-- The normalizer centralizer of the source actor a is a two-group in the
order-168 branch. This uses neither ambient simplicity nor actor fusion. -/
public theorem l27_actor_normalizer_centralizer_isPGroup
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    IsPGroup 2 ↥(centralizer ({into D k a} : Set G) ⊓ normalizer (E D k : Set G)) := by
  intro x
  let N := normalizer (E D k : Set G)
  let n : N := ⟨x.val, x.property.2⟩
  let aN : N := ⟨into D k a, centralizer_le_normalizer_E D k (k a).property⟩
  let q := eNormalizerBinaryAction D k
  have ha : q aN = twistedAction a.right := eNormalizerBinaryAction_local D k a.right
  have hcomm : n * aN = aN * n :=
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property.1)
  have hfour : q n ^ 4 = 1 := L27NormalizerActors.centralizing_a_fourth (q n)
    (eNormalizerBinaryAction_parity_of_168 D k h168 n)
    (by simpa only [map_mul, ha] using congrArg q hcomm)
  have hnE : (n : G) ^ 4 ∈ E D k := by
    have hnker : n ^ 4 ∈ q.ker := by
      change q (n ^ 4) = 1
      rwa [map_pow]
    rw [eNormalizerBinaryAction_ker] at hnker
    exact hnker
  let := E_elementary D k
  have htwo : ((n : G) ^ 4) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ hnE
  refine ⟨3, ?_⟩
  apply Subtype.ext
  change (n : G) ^ (4 * 2) = 1
  rwa [pow_mul]

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
