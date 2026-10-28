module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramSource

/-!
# Preserving the actual source factor during prime-pair selection

The rank-one source branches select an actual C-component of H, including
its residual in the single-component case. The diagram branches instead
select a parabolic factor whose intrinsic PSL₂ quotient has the same field
as the literal PSL₃, SL₃ or Sp₄ residual quotient. All these identifications
survive selection of the prime pair; no identification of a parabolic with
an H-component or of the left and right field degrees is made.

These are the source alternatives needed by the changed-Sylow component
sieve in original 5.2.2. They follow from the existing concrete factor
constructors, with the scalar cover retained at field four.
Source: Aschbacher–Smith E.2.2 and 5.1.10–11, applied in 5.2.2,
printed pp.215–216,634–635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- Either the selected factor is an actual H-component, or its intrinsic
rank-one field is the field of the original classical rank-two residual. -/
@[expose] def SelectedSourceModels (H R : Subgroup G) : Prop :=
  (R.subgroupOf H).IsCComponent ∨
    ∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
       Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
       ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))

/-- Construct the prime pair and retain the source alternative on that same
factor. All relative components and intrinsic quotients refer to the original H. -/
theorem source_prime_pair_selected_models
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R := by
  rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hpar with hs | hs
  · obtain ⟨C,f,hC,hqs,hgen,_,hc | hc⟩ := hs
    · refine ⟨C.map H.subtype,
        (exchanged_source_rightData h hH hpar c hC hgen hc.1 hc.2).localData h hH c hd,
        Or.inl ?_⟩
      change ((C.map H.subtype).comap H.subtype).IsCComponent
      rwa [comap_map_eq_self_of_injective H.subtype_injective]
    · refine ⟨residual H,(single_bender_prime_pair h hH c hd hC hqs hc.1 hc.2).1,
        Or.inl ?_⟩
      have he : C = pResidual 2 H :=
        BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hC
      change (((pResidual 2 H).map H.subtype).comap H.subtype).IsCComponent
      rw [comap_map_eq_self_of_injective H.subtype_injective,←he]
      exact hC
  · obtain ⟨C,f,hC,hqs,_,hf,hc,hm⟩ := hs
    have hres := diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hC hqs hc hf hm
    rcases hm with ⟨F,_,_,_,_,hF,e,he,hmove⟩ | ⟨F,_,_,_,_,hF,e,he,hmove⟩
    · obtain ⟨R,hr⟩ := linear_source_rightData_of_nonprojective_four h.sylow_normalizes
        hH hpar hthree c hC hqs hc hf hF e he hmove
      exact ⟨R true,(hr true).1.localData h hH c hd,Or.inr ⟨f,hf,(hr true).2,hres⟩⟩
    · obtain ⟨R,hr⟩ := symplectic_source_rightData h.sylow_normalizes hH hpar c hC hqs hc hf hF e he hmove
      exact ⟨R true,(hr true).1.localData h hH c hd,Or.inr ⟨f,hf,(hr true).2,hres⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
