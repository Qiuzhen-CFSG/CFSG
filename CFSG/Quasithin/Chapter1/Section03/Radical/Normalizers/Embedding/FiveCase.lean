module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.SourceKernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.ResidualEquality

/-!
# The surviving case-(10) radical embedding

From the actual source setup and case (10) for the images in N/O₂(N),
we obtain p = s = r = 5, K/O₂(K) ≃ PSL₃(5), Y = L_C, and the exact
odd Fitting-prime support of L_C/O₂(L_C). Every chosen Sylow p-subgroup
of Ξ_p(L) gives the marked elementary kernel in K/O₂(K).

The SL₂ section of L/O₂,F(L) forces the case parameter to be five.
Normality and the Ξ quotient shape then identify the actual Sylow image
with the elementary kernel. The PSL₃(5) order bound and A.3.6 determine
the residual quotient order; Sylow normalization and perfectness lift
the comparison to equality of the original residuals.

Only the exact universal earlier A.3.6 statement remains a parameter.
The preceding source reductions and selection of case (10) are inputs;
parabolic recognition consumes the marked conclusion in a separate module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
1.3.8, printed pp.512–513, and A.3.6/A.3.12(10), printed pp.43–47.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every chosen Sylow image is the specified case-(10) kernel in the
actual normalizer quotient. No replacement of the chosen Sylow is made. -/
theorem SourceData.caseTen_sylow_image_eq_kernel {𝒦 : GroupClass.{u}} {p r s : ℕ}
    {L : Subgroup G} {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)}
    {K : Subgroup G} (h : SourceData 𝒦 p r L T C K)
    (hcase : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s)
    (P : Sylow p (XiP p L))
    (U : Subgroup (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G)))) [U.Normal]
    (hU : ElementaryModel s 2 U)
    (e : (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) ⧸ U ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :
    (quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype)
      (normalizer (C.map (radicalCore p L T).subtype : Set G))).subgroupOf
        (quotientImage (normalizerResidual L (radicalCore p L T))
          (normalizer (C.map (radicalCore p L T).subtype : Set G))) = U := by
  obtain ⟨_, hs, hmark⟩ := h.caseTen_primes_and_marking hcase
  have hm := (markedFiveExtension_componentQuotient_iff h.contains_Y
    ((map_subtype_le _).trans (h.contains_xi.trans h.contains_Y))
    h.component.1 h.component.2).mp (hmark P)
  obtain ⟨hPB, hP, hn, _⟩ := hm
  let := hn
  have hc : Nat.card ((quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype)
      (normalizer (C.map (radicalCore p L T).subtype : Set G))).subgroupOf
        (quotientImage (normalizerResidual L (radicalCore p L T))
          (normalizer (C.map (radicalCore p L T).subtype : Set G)))) = 25 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv]
    exact elementary_card hP
  have hle := odd_normal_le_kernel hcase.prime hcase.large U _ e
    (show Odd (Nat.card _) from hc ▸ (by decide : Odd 25))
  apply eq_of_le_of_card_ge hle
  rw [elementary_card hU, hs, hc]
  decide

/-- The conditional case-(10) deduction in the proof of 1.3.8. All prime,
model, residual and marking conclusions are proved from the source inputs.
The universal A.3.6 parameter retains its complete source hypotheses. -/
theorem SourceData.caseTen_deduction {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ D : Subgroup E,
      D.IsCComponent → A36Conclusion D)
    {p r s : ℕ} {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (hcase : CaseTen
      (quotientImage (normalizerResidual L (radicalCore p L T))
        (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) s) :
    p = 5 ∧ s = 5 ∧ r = 5 ∧
      Nonempty (XiQuotient K ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) ∧
      normalizerResidual L (radicalCore p L T) =
        normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      (∀ q : ℕ, q.Prime → Odd q →
        (q ∣ Nat.card (fittingSubgroup (XiQuotient
          (normalizerResidual L (C.map (radicalCore p L T).subtype)))) ↔ q = 5)) ∧
      ∀ P : Sylow p (XiP p L),
        MarkedFiveExtension (quotientImage (normalizerResidual L (radicalCore p L T)) K)
          (quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K) := by
  obtain ⟨hp, hs, hmark⟩ := h.caseTen_primes_and_marking hcase
  subst s
  let : Fact p.Prime := ⟨h.prime⟩
  let P : Sylow p (XiP p L) := Classical.choice inferInstance
  obtain ⟨heq, hsupport⟩ :=
    ResidualEquality.residual_equality_and_fitting_support hA36 h hp hcase P (hmark P)
  exact ⟨hp, rfl, parameter_eq_five h.prime_r L h.nilpotent h.quotient_r,
    component_model_five h.component.1 h.component.2 hcase.large_model,
    heq, hsupport, hmark⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
