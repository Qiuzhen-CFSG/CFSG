module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Application

/-!
# Cartan escape in the original A₅ terminal context

An actual HStar member outside N_G(L) supplies a second maximal two-local
subgroup over T. The original chosen module and A₅ quotient therefore
satisfy the generic Cartan source hypotheses at exponent two. The proved
Cartan preparation supplies both Hall subgroups before residual normalization.

The generic exceptional output lives on the whole reduced module. We use
the original chosen A₅ marking for its module clause at V, and transport the
full relative component and its actual A₇, J₂ or M₂₃ quotient isomorphism to
the literal omega centralizer in `Source523.LocalAlternative`. This retains
the original residual and the mapped relative normalizer N_L(T ∩ L).

The local 5.1.13 and local-to-global 5.2.2 implications remain explicit.
Their shared producer is `qt-d-1222-rankone-exceptional-cartan-analysis`.
The final theorem also retains the independent normalized global branch;
`qt-d-13627-components` and `qt-d-1361-source` own final terminal assembly.
This file proves the adapter, not the still-pending source classification.

Source: Aschbacher–Smith, 5.2.2–3, printed pp.646–649, and the application
in 13.6.27 and the terminal contradiction, printed pp.934–935.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Chapter12.Section02 Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

private theorem many_maximal_overgroups_of_hstar (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  obtain ⟨hM, hTM, _⟩ := RankOneModule.normalizer_configuration d.chosen
    (original_hypothesis1223 d).toHypothesis1221
  have hc : pCore 2 H ≠ ⊥ := by
    intro hb
    apply hH.1.1.1
    simp only [Subgroup.pCoreIn, hb, Subgroup.map_bot]
  obtain ⟨N, hN, hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hc
  apply Set.one_lt_ncard_iff_nontrivial.mpr
  refine ⟨normalizer (L : Set G), ⟨hM, hTM⟩, N, ⟨hN, hH.1.1.2.trans hHN⟩, ?_⟩
  intro he
  exact hH.1.2 (he.symm ▸ hHN)

private theorem linear_quotient_of_context (d : Context T L V V₁ V₂ V₃) :
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2) := by
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by decide), ?_⟩
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact ⟨d.quotient.trans e.symm⟩

private theorem not_isPSL_three_of_no_L3Four {X : Type*} [Group X]
    (h : ¬ Nonempty (X ≃* L3Four)) : ¬ ClassicalGroup.IsPSL X 3 4 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let := Fintype.ofFinite F
  let := Fintype.ofFinite F4
  let eF : F ≃+* F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact (GaloisField.card 2 2 (by decide)).symm)
  exact h ⟨e.trans (Atlas.fieldEquivPSL 3 eF)⟩

private theorem a5ModuleSum_of_context (d : Context T L V V₁ V₂ V₃) : Source523.A5ModuleSum L V := by
  let ev : Multiplicative (Fin 1 → BinaryPermutation.core (Fin 5)) →*
      Multiplicative (BinaryPermutation.core (Fin 5)) := {
    toFun := fun v => Multiplicative.ofAdd (v.toAdd 0)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective ev := by
    intro x y h
    apply Multiplicative.toAdd.injective
    funext i
    have h0 := congrArg Multiplicative.toAdd h
    change x.toAdd 0 = y.toAdd 0 at h0
    simpa only [Fin.eq_zero] using h0
  have hs : Function.Surjective ev := fun x => ⟨Multiplicative.ofAdd (fun _ => x.toAdd), rfl⟩
  refine ⟨1, by decide, d.quotient, d.flag.module.map.comp ev,
    d.flag.module.injective.comp hi, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map]
    exact d.flag.module.range_eq
  · intro l v
    change MulAut.conj (l : G) (d.flag.module.map (Multiplicative.ofAdd (v 0))) =
      d.flag.module.map (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5)
          (d.quotient (QuotientGroup.mk' (pCore 2 L) l)).val (v 0)))
    rw [Context.quotient_mk]
    exact d.flag.module.equivariant l (v 0)

/-- Transport the full shared Cartan output to the chosen module and the
literal relative component required by source 5.2.3(1). -/
theorem source523_local_of_cartan_conclusion (d : Context T L V V₁ V₂ V₃)
    (he : CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H) :
    Source523.LocalAlternative T L H V 2 := by
  obtain ⟨_, hlinear, X, hRX, hXC, hX, hm⟩ := he
  let e := subgroupOfEquivOfLe hXC
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨rfl, a5ModuleSum_of_context d, X.subgroupOf (omegaCentralizer T), hX,
    ?_, Or.inl ⟨hlinear, ?_⟩⟩
  · simpa only [map_subgroupOf_eq_of_le hXC] using hRX
  · exact hm.imp (fun hf => hf.map (fun f => q.trans f))
      (fun hf => hf.imp (fun hf => hf.map (fun f => q.trans f))
        (fun hf => hf.map (fun f => q.trans f)))

/-- The exact nonnormalization branch consumed by `Source523Application`.
The original context and HStar membership discharge the generic ambient,
field and Cartan-preparation inputs. Only the two shared source arguments
remain explicit; no module or component conclusion is added as a premise. -/
theorem source523_local_of_cartan_escape (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four))
    (hescape : ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hlocal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    (hglobal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → A ≤ normalizer (residual H : Set G)) :
    Source523.LocalAlternative T L H V 2 := by
  have h := original_hypothesis1223 d
  have hpsl := linear_quotient_of_context d
  have he := d.chosen.rankOne_exceptional_cartan_of_source h (many_maximal_overgroups_of_hstar d hH)
    (by decide : 1 < 2) hpsl hH hgen (not_isPSL_three_of_no_L3Four hthree) hescape
    (fun _ hH' hgen' => d.chosen.rankOne_cartanPreparation h.toHypothesis1221
      (by decide : 1 < 2) hpsl hH' hgen') hlocal hglobal
  exact source523_local_of_cartan_conclusion d he.1

/-- Supply the escape callback of the actual terminal consumer. The
shared Cartan arguments and independent normalized global branch remain
with their source producers and must be discharged at final assembly. -/
theorem source_qtkeModel_of_cartan_sources (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hlocal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    (hglobal : ∀ H : Subgroup G,
      SourceLocalCartanEscape KnownSimple.IsKnownSimple G →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → A ≤ normalizer (residual H : Set G))
    (hnormalized : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
      ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) →
      (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
        normalizer ((pResidual 2 H).map H.subtype : Set G) →
      Source523.GlobalAlternative G) : ClassificationModels.IsQTKEModel G := by
  apply source_qtkeModel_of_residual_branches d hCv houtside hcounter ?_ hnormalized
  intro H hH _ hgen hthree hescape
  exact source523_local_of_cartan_escape d hH hgen hthree hescape hlocal (hglobal H)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
