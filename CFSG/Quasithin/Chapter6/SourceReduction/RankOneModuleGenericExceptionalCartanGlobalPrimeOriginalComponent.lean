module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowOrbit
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The original diagram component in the common overgroup

The diagram alternatives give a quasisimple quotient of the whole original
residual. Its two-perfectness therefore makes it a genuine C-component of H.
Applying source 1.2.4 to this component, with the original full Sylow T,
gives a normal overcomponent in X = ⟨N_G(T₀), H⟩. Uniqueness above the
selected parabolic R identifies it with the previously constructed common
component I. Hence O²(H) ≤ I and the T-orbit of I is just I.

The source pair retains this conclusion together with both Hall markings,
the smaller containing catalogue and the strict changed-orbit obstruction.
The selected R is not identified with the original component. Equality
of the original and changed residuals still requires the source structure
and Sylow-intersection argument.

Source: Aschbacher–Smith 1.2.4 and 5.2.2, printed pp.505 and 648–649
of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem diagram_model_quasisimple
    {Q : Type*} [Group Q] {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨
      Chapter1.Section02.LocalModels.IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) : IsQuasisimple Q := by
  rcases hm with ⟨F,_,_,_,⟨e⟩⟩ | ⟨F,_,_,_,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : IsQuasisimple SL(3,F) :=
      { toIsPerfect := Atlas.sl_perfect 3 (by decide)
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    let : IsQuasisimple PSL(3,F) := IsQuasisimple.of_surjective
      (QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _)
    exact IsQuasisimple.of_mulEquiv e.symm
  · let : IsQuasisimple SL(3,F) :=
      { toIsPerfect := Atlas.sl_perfect 3 (by decide)
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    exact IsQuasisimple.of_mulEquiv e.symm
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hlarge : 3 < Nat.card F := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
      omega
    let : IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F) :=
      Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.isQuasisimple hlarge
    exact IsQuasisimple.of_mulEquiv
      (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).symm

/-- The source diagram model makes the whole original residual a genuine
H-component, independently of the selected parabolic component. -/
theorem SelectedSourceModels.residual_component_of_not_right
    {H R : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) :
    ((residual H).subgroupOf H).IsCComponent := by
  obtain ⟨f,hf,_,hm⟩ := hs.resolve_left hn
  let := diagram_model_quasisimple hf hm
  have hc : (pResidual 2 H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (pResidual 2 H).Normal).isSubnormal (isPPerfect_pResidual 2)
  change (((pResidual 2 H).map H.subtype).comap H.subtype).IsCComponent
  rwa [comap_map_eq_self_of_injective H.subtype_injective]

/-- Above a parabolic right factor, the unique common overcomponent contains
the whole original residual and is normal in the literal common overgroup. -/
theorem LocalData.common_component_original_residual
    {T : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hc : ((residual H).subgroupOf H).IsCComponent)
    (hu : ∀ J : Subgroup G, J ≤ normalizer (normalizingSylow T R : Set G) ⊔ H →
      (J.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent →
      R ≤ J → J = I) :
    residual H ≤ I ∧
      (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).Normal := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ X := hTH.trans le_sup_right
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hH.1.1.1
      ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩ hKH hc
  have hlocalX : K.subgroupOf X ∈ Chapter1.L X ((T : Subgroup G).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp ⟨hKX,hlocal⟩
  have hQ := Chapter3.sqtk_of_mem_H h.qtke (d.common_normal_overgroup h hH c hd hz).1
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  have hn : ((T : Subgroup G).subgroupOf X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hKX]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  obtain ⟨J,⟨hJ,hKJ,hJn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQbar
      (T.subtype hTX) hlocalX hn
  have hJX : J.map X.subtype ≤ X := map_subtype_le _
  have hJlit : (J.map X.subtype).subgroupOf X = J :=
    comap_map_eq_self_of_injective X.subtype_injective J
  have hKJ' : K ≤ J.map X.subtype := by
    simpa only [map_subgroupOf_eq_of_le hKX] using map_mono (f := X.subtype) hKJ
  have he : J.map X.subtype = I :=
    hu _ hJX (hJlit.symm ▸ hJ) (d.right_le_residual.trans hKJ')
  refine ⟨hKJ'.trans_eq he,?_⟩
  rw [←he,hJlit]
  exact hJn

/-- Retain the source catalogue and original Hall markings on the same
selected R, with the original diagram residual inside its actual normal common component. -/
theorem source_prime_pair_original_component
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingSourceContainer X K) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n ∧
              ¬ (T : Subgroup G) ≤ normalizer (conjugateSpanBy R T₁ : Set G) ∧
              residual (R ⊔ T₁) ≠ residual H ∧
              let X := normalizer (normalizingSylow T R : Set G) ⊔ H
              ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
                normalizingSylow T R ≤ normalizer (I : Set G) ∧
                (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
                let Kplus := conjugateSpanBy I (T : Subgroup G)
                residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
                  T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ < Kplus ∧
                  (¬ (R.subgroupOf H).IsCComponent → residual H ≤ I ∧
                    (I.subgroupOf X).Normal ∧ Kplus = I ∧ conjugateSpanBy R T₁ < I))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_changedSylow_orbit h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with hsmall | ⟨U,hU,hlt,hm,hn,he,I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,hK0J⟩
  · exact .inl hsmall
  refine .inr ⟨U,hU,hlt,hm,hn,he,I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,hK0J,?_⟩
  intro hnot
  obtain ⟨hKI,hIn⟩ := d.common_component_original_residual h hH c hd hz
    (hs.residual_component_of_not_right hnot) hu
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ normalizer (normalizingSylow T R : Set G) ⊔ H :=
    hTH.trans le_sup_right
  have hTI' := hTX.trans ((normal_subgroupOf_iff_le_normalizer hIX).mp hIn)
  have horbit : conjugateSpanBy I (T : Subgroup G) = I :=
    le_antisymm (conjugateSpanBy_le le_rfl hTI') (le_conjugateSpanBy I _)
  exact ⟨hKI,hIn,horbit,horbit ▸ hK0J⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
