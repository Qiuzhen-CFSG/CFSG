module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.SourceData
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.Inversion

/-!
# Reduction of basic Ree involution ranks to binary odd-order actors

Coefficient base change commutes with the actual embedding into algebraic
F4. Every exceptional power fixes the embedded binary Ree subgroup
pointwise. Consequently its action on any exceptional factor is the
untwisted binary action, even though its ambient conjugating element can
change under the exceptional power. Conjugacy preserves fixed codimension.

If every involution inverts an odd actor from this subgroup and every such
actor moves at least twenty dimensions, the commutator inequality gives
the required ten-dimensional lower bound. The exported application uses
the literal `exceptionalFactor` and the factorization owner's coefficient
embedding. Both source inputs remain explicit and must be established
before this is an unconditional basic-factor bound.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal pp.57--58; GLS3, Corollary 2.8.6(b), for the exceptional factors.
-/

public section

open Theory.AlgebraicGroup Representation Subgroup
open ReeF4.BinaryDegree.ExceptionalTensor

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions

universe u

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The two literal coefficient embeddings agree on all split-group elements,
as follows from their root-generator formulas. -/
theorem splitEmbedding_comp_splitMap {k m : ℕ}
    (f : CoefficientField m →+* F) (e : CoefficientField k →+* CoefficientField m) :
    (Classification.splitEmbedding f).comp (Subfield.splitMap e) =
      Classification.splitEmbedding (f.comp e) := by
  apply splitGroup_hom_ext
  intro r t
  simp only [MonoidHom.comp_apply, Subfield.splitMap_rootGenerator,
    Classification.splitEmbedding_rootGenerator, RingHom.comp_apply]

/-- Every exceptional power fixes the actual binary subfield Ree subgroup. -/
theorem exceptional_pow_binary_subfield {m : ℕ}
    (e : CoefficientField 0 →+* CoefficientField m) (x : Model 0) (n : ℕ) :
    (exceptionalEndomorphism m ^ n)
        (toSplitGroup m (Subfield.reeMap (by simp) e x)) =
      Subfield.splitMap e (toSplitGroup 0 x) := by
  rw [Subfield.toSplitGroup_reeMap, ← Subfield.splitMap_exceptional_pow]
  have hx : exceptionalEndomorphism 0 (toSplitGroup 0 x) = toSplitGroup 0 x := by
    have h := reeTwist_toSplitGroup 0 x
    rw [reeTwist_eq_pow] at h
    change (exceptionalEndomorphism 0 ^ 1) (toSplitGroup 0 x) = toSplitGroup 0 x at h
    simpa only [pow_one] using h
  rw [Subfield.pow_apply_eq_of_apply_eq _ hx n]

/-- Evaluation of every twisted algebraic factor on the binary subfield is
the exact untwisted action through the composed coefficient homomorphism. -/
theorem restricted_action_binary_subfield {m : ℕ} (B : AlgebraicFactor F)
    (f : CoefficientField m →+* F) (e : CoefficientField 0 →+* CoefficientField m)
    (x : Model 0) (n : ℕ) :
    (B.restrict ((Classification.splitEmbedding f).comp
      ((exceptionalEndomorphism m ^ n).comp (toSplitGroup m)))).ρ
        (Subfield.reeMap (by simp) e x) =
      (B.restrict ((Classification.splitEmbedding (f.comp e)).comp (toSplitGroup 0))).ρ x := by
  change (B.action.action ((Classification.splitEmbedding f)
    ((exceptionalEndomorphism m ^ n)
      (toSplitGroup m (Subfield.reeMap (by simp) e x)))) : Module.End F B.Space) =
    (B.action.action ((Classification.splitEmbedding (f.comp e)) (toSplitGroup 0 x)) :
      Module.End F B.Space)
  rw [exceptional_pow_binary_subfield]
  have h := DFunLike.congr_fun (splitEmbedding_comp_splitMap f e) (toSplitGroup 0 x)
  change Classification.splitEmbedding f (Subfield.splitMap e (toSplitGroup 0 x)) = _ at h
  rw [h]

/-- Conditional assembly of the basic-factor bound. The premises are the
independent group coverage and binary odd-element calculations in `SourceData`. -/
theorem basic_involution_bound_of_binary_odd_bounds {m : ℕ}
    (hcoverage : BinaryOddInversionCoverage m) (hodd : BinaryOddDisplacement F)
    (f : CoefficientField m →+* F) (B : AlgebraicFactor F)
    (hB : B.IsExceptionalBasic) (hdim : 26 ≤ Module.finrank F B.Space)
    (i : ZMod (2 * m + 1)) (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp
        ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ.comp
          (zpowers t).subtype)) := by
  obtain ⟨e, x, c, hx, hinv⟩ := hcoverage t ht ht2
  let j : Model 0 →* Model m := Subfield.reeMap (by simp) e
  let ρ : Representation F (Model m) B.Space :=
    (B.restrict ((Classification.splitEmbedding f).comp
      ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ
  have horder : orderOf (c * j x * c⁻¹) = orderOf x := by
    exact ((MulAut.conj c).orderOf_eq (j x)).trans
      (orderOf_injective j (Subfield.reeMap_injective (by simp) e) x)
  have ho : Odd (orderOf (c * j x * c⁻¹)) := by
    rw [horder]
    rcases hx with hx | hx <;> rw [hx] <;> decide
  have htwice := cyclic_fixedCodim_le_twice_of_inverts ρ t (c * j x * c⁻¹) ho hinv
  rw [cyclic_fixedCodim_conj] at htwice
  have hr := hodd B hB hdim (f.comp e) x hx
  let σ : Representation F (Model 0) B.Space :=
    (B.restrict ((Classification.splitEmbedding (f.comp e)).comp (toSplitGroup 0))).ρ
  change 20 ≤ Module.finrank F (B.Space ⧸ invariants (σ.comp (zpowers x).subtype)) at hr
  rw [cyclic_fixedCodim_eq_rank σ x] at hr
  rw [cyclic_fixedCodim_eq_rank ρ (j x)] at htwice
  have he := restricted_action_binary_subfield B f e x i.val
  change ρ (j x) = _ at he
  rw [he] at htwice
  change 10 ≤ Module.finrank F (B.Space ⧸ invariants (ρ.comp (zpowers t).subtype))
  change 20 ≤ Module.finrank F (LinearMap.range (σ x - 1)) at hr
  change Module.finrank F (LinearMap.range (σ x - 1)) ≤ _ at htwice
  omega

/-- The local-rank premise in the tensor estimate, on its literal exceptional
factor and the factorization owner's canonical coefficient embedding. -/
theorem exceptionalFactor_involution_bound_of_binary_odd_bounds [CharP F 2] {m : ℕ}
    (hcoverage : BinaryOddInversionCoverage m) (hodd : BinaryOddDisplacement F)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic) (i : ZMod (2 * m + 1))
    (hdim : 26 ≤ Module.finrank F (B i).Space)
    (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ Module.finrank F
      ((exceptionalFactor (Classification.splitEmbedding (Classification.coefficientHom F m)) B i) ⧸
        invariants ((exceptionalFactor
          (Classification.splitEmbedding (Classification.coefficientHom F m)) B i).ρ.comp
            (zpowers t).subtype)) :=
  basic_involution_bound_of_binary_odd_bounds hcoverage hodd
    (Classification.coefficientHom F m) (B i) (hB i) hdim i t ht ht2

end ReeF4.FixedSpaceEstimate.BasicInvolutions
