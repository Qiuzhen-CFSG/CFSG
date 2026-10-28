module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Containment
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Recognizing the original tetrahedral factors

A quotient onto S₆ sends a Sylow two-subgroup and its generating index-three
overgroups to the same configuration. The kernel lies in the Sylow subgroup,
so both relative indices are preserved. The embedded two-residual of `Y_i T_I`
is `Y_i`, and residuals commute with the quotient map. The established S₆
residual-pair theorem therefore recognizes both quotient images as A₄.
Injectivity on each factor lifts these to actual multiplicative equivalences
of the original factors. The component quotient is a two-group, so the
coordinates themselves force containment of every two-perfect factor.

In the component application, faithfulness on `L` and the containments
`Y_i ≤ L` supply this injectivity. Constructing the compatible coordinates from the raw configuration remains
an upstream obligation; the conditional corollaries do not discharge it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed p.1163.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals

/-- Recognize the original factors, rather than only their quotient images.
The injectivity hypotheses must be discharged by their containment in the
selected component and the faithful restriction of the quotient map. -/
theorem factors_equiv_alternating_four
    {I : Type*} [Group I] [Finite I] (T : Sylow 2 I) (Y₁ Y₂ : Subgroup I)
    (q : I →* S6) (hq : Function.Surjective q) (hk : q.ker ≤ (T : Subgroup I))
    (h₁ : IsPPerfect 2 Y₁) (h₂ : IsPPerfect 2 Y₂)
    (hn₁ : (T : Subgroup I) ≤ normalizer (Y₁ : Set I))
    (hn₂ : (T : Subgroup I) ≤ normalizer (Y₂ : Set I))
    (hi₁ : (T : Subgroup I).relIndex (Y₁ ⊔ (T : Subgroup I)) = 3)
    (hi₂ : (T : Subgroup I).relIndex (Y₂ ⊔ (T : Subgroup I)) = 3)
    (hgen : (Y₁ ⊔ (T : Subgroup I)) ⊔ (Y₂ ⊔ (T : Subgroup I)) = ⊤)
    (hj₁ : Function.Injective (q.comp Y₁.subtype))
    (hj₂ : Function.Injective (q.comp Y₂.subtype)) :
    Nonempty (Y₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (Y₂ ≃* alternatingGroup (Fin 4)) := by
  let P := T.mapSurjective hq
  let H₁ := (Y₁ ⊔ (T : Subgroup I)).map q
  let H₂ := (Y₂ ⊔ (T : Subgroup I)).map q
  have hp : (P : Subgroup S6) = (T : Subgroup I).map q := rfl
  have hm₁ : (P : Subgroup S6) ≤ H₁ := by
    rw [hp]
    exact map_mono le_sup_right
  have hm₂ : (P : Subgroup S6) ≤ H₂ := by
    rw [hp]
    exact map_mono le_sup_right
  have hii₁ : (P : Subgroup S6).relIndex H₁ = 3 := by
    rw [hp, relIndex_map_map, sup_of_le_left hk,
      sup_of_le_left (hk.trans le_sup_right)]
    exact hi₁
  have hii₂ : (P : Subgroup S6).relIndex H₂ = 3 := by
    rw [hp, relIndex_map_map, sup_of_le_left hk,
      sup_of_le_left (hk.trans le_sup_right)]
    exact hi₂
  have hgg : H₁ ⊔ H₂ = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q hq]
  have hr (Y : Subgroup I) (hy : IsPPerfect 2 Y)
      (hn : (T : Subgroup I) ≤ normalizer (Y : Set I)) :
      (pResidual 2 ((Y ⊔ (T : Subgroup I)).map q)).map
        ((Y ⊔ (T : Subgroup I)).map q).subtype = Y.map q := by
    rw [← map_embedded_pResidual, embedded_pResidual_join_pGroup Y (T : Subgroup I)
      hy T.isPGroup' hn]
  have h := ResidualPairRecognition.residual_pair_recognition P H₁ H₂ hm₁ hm₂ hii₁ hii₂ hgg
  dsimp only at h
  change Nonempty (Y₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (Y₂ ≃* alternatingGroup (Fin 4))
  change Nonempty (((pResidual 2 ((Y₁ ⊔ (T : Subgroup I)).map q)).map
      ((Y₁ ⊔ (T : Subgroup I)).map q).subtype) ≃* alternatingGroup (Fin 4)) ∧ _ at h
  rw [hr Y₁ h₁ hn₁, hr Y₂ h₂ hn₂] at h
  have lift (Y : Subgroup I) (hj : Function.Injective (q.comp Y.subtype)) :
      Y ≃* Y.map q :=
    MulEquiv.ofBijective (q.subgroupMap Y)
      ⟨fun _ _ he => hj (congrArg Subtype.val he), q.subgroupMap_surjective Y⟩
  exact ⟨h.1.map fun e => (lift Y₁ hj₁).trans e,
    h.2.1.map fun e => (lift Y₂ hj₂).trans e⟩

/-- Once the component and quotient coordinates have been constructed,
component containment gives both A₄ identifications. -/
theorem factors_equiv_of_coordinates
    {I : Type*} [Group I] [Finite I] (T : Sylow 2 I) (L Y₁ Y₂ : Subgroup I)
    (d : QuotientCoordinates L) (hY₁L : Y₁ ≤ L) (hY₂L : Y₂ ≤ L)
    (h₁ : IsPPerfect 2 Y₁) (h₂ : IsPPerfect 2 Y₂)
    (hn₁ : (T : Subgroup I) ≤ normalizer (Y₁ : Set I))
    (hn₂ : (T : Subgroup I) ≤ normalizer (Y₂ : Set I))
    (hi₁ : (T : Subgroup I).relIndex (Y₁ ⊔ (T : Subgroup I)) = 3)
    (hi₂ : (T : Subgroup I).relIndex (Y₂ ⊔ (T : Subgroup I)) = 3)
    (hgen : (Y₁ ⊔ (T : Subgroup I)) ⊔ (Y₂ ⊔ (T : Subgroup I)) = ⊤) :
    Nonempty (Y₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (Y₂ ≃* alternatingGroup (Fin 4)) :=
  factors_equiv_alternating_four T Y₁ Y₂ d.quotientMap d.quotientMap_surjective
    (d.kernel_le_sylow T) h₁ h₂ hn₁ hn₂ hi₁ hi₂ hgen
    (d.factor_map_injective hY₁L) (d.factor_map_injective hY₂L)

/-- Compatible coordinates and the source two-perfectness suffice for both
original A₄ identifications; factor containment is derived. -/
theorem factors_equiv_from_coordinates
    {I : Type*} [Group I] [Finite I] (T : Sylow 2 I) (L Y₁ Y₂ : Subgroup I)
    (d : QuotientCoordinates L)
    (h₁ : IsPPerfect 2 Y₁) (h₂ : IsPPerfect 2 Y₂)
    (hn₁ : (T : Subgroup I) ≤ normalizer (Y₁ : Set I))
    (hn₂ : (T : Subgroup I) ≤ normalizer (Y₂ : Set I))
    (hi₁ : (T : Subgroup I).relIndex (Y₁ ⊔ (T : Subgroup I)) = 3)
    (hi₂ : (T : Subgroup I).relIndex (Y₂ ⊔ (T : Subgroup I)) = 3)
    (hgen : (Y₁ ⊔ (T : Subgroup I)) ⊔ (Y₂ ⊔ (T : Subgroup I)) = ⊤) :
    Nonempty (Y₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (Y₂ ≃* alternatingGroup (Fin 4)) :=
  factors_equiv_alternating_four T Y₁ Y₂ d.quotientMap d.quotientMap_surjective
    (d.kernel_le_sylow T) h₁ h₂ hn₁ hn₂ hi₁ hi₂ hgen
    (d.factor_map_injective (d.factor_le_component Y₁ h₁))
    (d.factor_map_injective (d.factor_le_component Y₂ h₂))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals
