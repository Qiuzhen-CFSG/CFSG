module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.QuotientPair
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Normalizer

/-!
# Closing the genuine Held normalizer enlargement

For E = <N_G(T₁),H>, K = <O²(H)^E> and the literal R = T₁ ∩ K,
the original quotient action preserves R/O₂(K). In the Held row the full
Sylow image and original odd complement form an irreducible Held pair,
whose two-residual is the image of O²(H). Its residual two-core lies in
the source parabolic core, hence in R/O₂(K). The model interval-normalizer
theorem therefore preserves the residual image, and kernel normalization
lifts this to the original O²(H).

Thus a strict enlargement can only be one of the three classical rows.
This proves the retained Held branch, rather than dropping it from the
corrected intrinsic catalogue. The classical rows and final assembly remain
with qt-d-10-nona5-half-sylow-unique. Source: Aschbacher--Smith 10.2.4--5,
printed pp.747--748, with the Held correction in quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- The actual classical component models remaining after the Held calculation.
Every model is an isomorphism of the literal two-core quotient; the invariant
rows also retain the full automorphism quotient of IT. -/
@[expose] def ClassicalClosureModel (T : Sylow 2 G) (I : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 (2 ^ n)) ∨
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p) ∨
        ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
          ∃ k : ℕ, (k = 4 ∨ k = 5) ∧ ClassicalGroup.IsPSL (XiQuotient I) k 2 ∧
            Nonempty (((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
              pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃*
              MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2))))

/-- The full normalizer preserves the actual parabolic residual in the Held
row. All pair, irreducibility, index and model-action premises are discharged. -/
theorem Data.normalizes_residual_of_held (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hq : IsQuasisimple (XiQuotient (enlargedResidual T L H)))
    (hm : Nonempty (XiQuotient (enlargedResidual T L H) ≃* Held.He)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  by_contra hN
  obtain ⟨S,P,hS,hpair,hirr,hres⟩ := h.exists_quotient_pair hn hq hN
  let X := quotientImage (enlargedResidual T L H) (residual H)
  let U := quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)
  have hUS : U ≤ (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (inf_le_left.trans inf_le_left))
  have hindex : U.relIndex (S : Subgroup (XiQuotient (enlargedResidual T L H))) ≤ 2 := by
    rw [hS]
    exact h.quotient_intersection_index hn
  have hcore : X.pCoreIn 2 ≤ U := by
    have hXN : (X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))) ≤
        normalizer (X : Set (XiQuotient (enlargedResidual T L H))) := by
      have hnX := le_normalizer_embedded_pResidual 2
        (X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))))
      have heX : (pResidual 2 (X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) :
          Subgroup (XiQuotient (enlargedResidual T L H)))).map
          (X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))).subtype = X := by
        rw [hS]
        exact h.quotient_parabolic_residual
      rwa [heX] at hnX
    have hc := pCoreIn_mono_of_normalizes (show X ≤ X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) from le_sup_left) hXN (p := 2)
    apply hc.trans
    rw [hS]
    exact h.quotient_parabolic_core_le_intersection
  apply hN
  apply h.normalizes_residual_of_quotientAction
  intro g
  exact SporadicRemaining.HeldPairs.preserves_residual_of_equiv hpair hirr hm.some
    hres hcore hUS hindex (quotientAction T L H g) (h.quotientAction_preserves_intersection g)

/-- Failure of residual normalization leaves only the three classical rows;
the additional genuine Held alternative has been excluded on its source input. -/
theorem Data.strict_classical_models (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    residual H < enlargedResidual T L H ∧ ∃ I : Subgroup G,
      I ∈ cComponentsIn (enlargement T L H) ∧ IsQuasisimple (XiQuotient I) ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      ClassicalClosureModel T I := by
  obtain ⟨hlt,I,hI,hq,hK,hm⟩ := h.strict_models hn hN
  refine ⟨hlt,I,hI,hq,hK,?_⟩
  rcases hm with hm | hm | hm | ⟨hi,he⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr hm)
  · have horbit : componentOrbit I (T : Subgroup G) = I :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer I T I le_rfl hi)
        (le_componentOrbit I T)
    have hKI := hK.trans horbit
    have hqK : IsQuasisimple (XiQuotient (enlargedResidual T L H)) := hKI.symm ▸ hq
    have heK : Nonempty (XiQuotient (enlargedResidual T L H) ≃* Held.He) := hKI.symm ▸ he
    exact (hN (h.normalizes_residual_of_held hn hqK heK)).elim

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
