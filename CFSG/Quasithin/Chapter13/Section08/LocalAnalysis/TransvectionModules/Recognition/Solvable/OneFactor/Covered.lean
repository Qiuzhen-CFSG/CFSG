module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.ResidualTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.MovedSpace
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
public import Theory.SpecificGroups.SymmetricTwoResidual


/-!
# The covered one-factor residual and moved space

For the actual covered natural flag, the earlier factorization 13.2.2(3)
gives two marked cubic directions in L₁/O₂(L₁). The residual of the actual
preimage of K* is normalized by H and has cubic quotient because K* is S₃.
Once O²(K*) lies in L₁*, the two-perfect lifting argument puts O²(K) in
L₁. Its quotient image is T-invariant and therefore one of the two marks.
Uniqueness of two-perfect lifts identifies O²(K) with L₀ or L₁,+.

In the latter case the proved action of L₁,+ on the natural flag generates
V₃/V₁. The natural one-factor moved space has dimension two, so it equals
the literal seedSpace in U_H/V₁. No moved-space or plus-action conclusion
is assumed. The normal-S₃ placement O²(K*) ≤ L₁* remains explicit; these
conditional theorems do not yet assert the exhaustive source alternative.

Source: Aschbacher–Smith, proof of 13.8.5, printed pp.947–948 (PDF
pp.964–965), using Notation 13.2.1 and 13.2.2(3), printed p.877. All reused
LocalAction results are intrinsic consequences of its earlier natural
setup, independent of the later component conclusions.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

private theorem residual_card_of_symmetricThree {A : Type*} [Group A] [Finite A]
    (e : A ≃* Equiv.Perm (Fin 3)) : Nat.card (pResidual 2 A) = 3 := by
  rw [Nat.card_congr ((pResidual 2 A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
    map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    Equiv.Perm.twoResidual_eq_alternating]
  rw [Nat.card_eq_fintype_card]
  decide

variable {G : Type*} [Group G] [Finite G] {H L V V₁ V₃ : Subgroup G}

/-- The literal covered star image has three-rank at least two. Its
elementary-nine quotient is constructed by the marked model; passage to
H/O₂(H) preserves the needed odd-rank lower bound. -/
theorem covered_star_threeRank_ge_two (T : Subgroup G) (d : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) (hLH : one L T V₁ ≤ H) :
    2 ≤ primeRank 3 (Source.starImage H (one L T V₁)) := by
  let Q := one L T V₁ ⧸ pCore 2 (one L T V₁)
  let : IsMulCommutative Q := d.one_quotient_commutative hfactor
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hr : 2 ≤ primeRank 3 Q := primeRank_ge_of_elementary_embedding
    (d.one_quotient_cube hfactor) (d.one_quotient_card hfactor) (MonoidHom.id Q) Function.injective_id
  have he := primeRank_congr 3 (starCoreQuotientEquiv H (one L T V₁) hLH)
  change primeRank 3 Q = _ at he
  rw [he] at hr
  exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)

/-- The actual preimage residual is a marked source lift once its image
is contained in L₁*. The invariant cubic direction and all lifting
identifications are proved here. -/
theorem covered_residual_eq_zero_or_plus (T : Sylow 2 G) (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (hLH : one L (T : Subgroup G) V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (K : Subgroup (Source.Hstar H)) [K.Normal] (e : K ≃* Equiv.Perm (Fin 3))
    (hplace : (pResidual 2 K).map K.subtype ≤ Source.starImage H (one L (T : Subgroup G) V₁)) :
    preimageResidual H K = zero L ∨ preimageResidual H K = plus L (T : Subgroup G) V₁ := by
  let Y := one L (T : Subgroup G) V₁
  let R := preimageResidual H K
  have hR : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 _
  have hnR : H ≤ normalizer (R : Set G) := le_normalizer_preimageResidual H K
  have hRH : R ≤ H := (preimageResidual_le H K).trans (starPreimage_le H K)
  have hRY : R ≤ Y := preimageResidual_le_of_image H K Y hLH
    (isPPerfect_embedded_pResidual 2 _)
    ((core_le_sourceSylow H T hTH).trans (T_normalizes_one L _ V₁ d.line_stable)) hplace
  have hc : Nat.card (Source.starImage Y R) = 3 := by
    rw [← Nat.card_congr (normalStarEquiv Y R hRY
      (localImage_normal Y R hRY (hLH.trans hnR))).toEquiv,
      Nat.card_congr (normalStarEquiv H R hRH
        (localImage_normal H R hRH hnR)).toEquiv]
    change Nat.card (Source.starImage H (preimageResidual H K)) = 3
    rw [starImage_preimageResidual,
      ← Nat.card_congr ((pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv]
    exact residual_card_of_symmetricThree e
  have hs : ∀ s : (T : Subgroup G), ∀ x ∈ Source.starImage Y R,
      coreAction Y ⟨s.val, T_normalizes_one L _ V₁ d.line_stable s.property⟩ x ∈
        Source.starImage Y R := by
    rintro s x ⟨r, hr, rfl⟩
    rw [coreAction_mk]
    refine ⟨Y.normalizerMonoidHom
      ⟨s.val, T_normalizes_one L _ V₁ d.line_stable s.property⟩ r, ?_, rfl⟩
    exact (mem_normalizer_iff.mp (hnR (hTH s.property)) r.val).mp hr
  have hm := d.invariant_marked_line hfactor (Source.starImage Y R) hc hs
  rcases hm with hzero | hplus
  · left
    rw [zeroCoreMap, localCoreMap_range] at hzero
    exact eq_of_starImage_eq Y R (zero L) hRY
      (zero_le_one_of_factorization L _ V₁ hfactor) hR (isPPerfect_embedded_pResidual 2 _)
      ((pCoreIn_le 2 Y).trans (hLH.trans hnR))
      ((pCoreIn_le 2 Y).trans (one_normalizes_zero L _ V₁ d.normalizes_L)) hzero
  · right
    rw [plusCoreMap, localCoreMap_range] at hplus
    exact eq_of_starImage_eq Y R (plus L (T : Subgroup G) V₁) hRY
      (plus_le_one L _ V₁ d.line_stable) hR (isPPerfect_embedded_pResidual 2 _)
      ((pCoreIn_le 2 Y).trans (hLH.trans hnR))
      ((pCoreIn_le 2 Y).trans (one_normalizes_plus L _ V₁)) hplus

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] [Finite G] {H L V V₁ V₃ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The covered source branch, retaining the cover witness and deriving the
literal moved space from the marked action. Residual placement remains
the separate normal-S₃ group-theoretic obligation. -/
theorem covered_alternatives_of_residual_image_le (T : Sylow 2 G) (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (hLH : one L (T : Subgroup G) V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (factors : ChapterB.SolvableFFFactors (ρ.comp K.subtype))
    (hJ : offenderSubgroup (ρ.comp K.subtype) = ⊤) (hc : factors.count = 1)
    (hplace : (pResidual 2 K).map K.subtype ≤ Source.starImage H (one L (T : Subgroup G) V₁)) :
    (preimageResidual H K = zero L ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) ∨
    (preimageResidual H K = plus L (T : Subgroup G) V₁ ∧
      subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) := by
  let n := naturalTwo_of_count_one K factors hJ hc
  let e := n.groupEquiv.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
  rcases covered_residual_eq_zero_or_plus T d hfactor hLH hTH K e hplace with hzero | hplus
  · exact Or.inl ⟨hzero, ⟨d.cover⟩⟩
  · refine Or.inr ⟨hplus, ?_⟩
    apply movedSpace_eq_seedSpace_of_residual ρ hρ d.line_le_seed h₁ h₃ K factors hJ hc _ hplus
    rw [commutator_comm]
    exact d.seed_le_plus_commutator_sup hfactor
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

end
