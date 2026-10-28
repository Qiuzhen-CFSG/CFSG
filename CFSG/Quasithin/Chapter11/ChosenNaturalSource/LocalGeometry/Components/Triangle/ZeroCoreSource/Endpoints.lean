module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.OriginalSetup
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# Characteristic two and the generated-group core reduction

The original seed lies in S₀ = O₂(XT). Each endpoint contains and normalizes
its nonzero original flag term. Its join with T therefore belongs to H(T);
relative normality and the Chapter 1 inheritance theorem give characteristic
two for the full endpoint itself.

The F.1.1-generated group J = ⟨K₀,L₂,S₀⟩ is normal in the original
H = JX, since X normalizes all three generators. Thus absence of the common
normal Q forces O₂(H) = 1 and then O₂(J) = 1, with both full kernels retained.
The opposite-Borel comparison needed to identify F.1.1's parabolics with
the endpoints is not assumed or asserted here.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.762, verification of the zero-core case before F.1.9.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
@[expose] public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

include S in
/-- The retained seed, including its fixed layer, lies in the actual S₀. -/
theorem seed_le_commonTwo {X : Subgroup G} (hX : IsCartan T L X) :
    V ≤ commonTwo T X := by
  let := D.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (D.le_sylow.trans le_sup_right)
    (sup_le ((hX.1.trans inf_le_left).trans D.normalizes) S.sylow_normalizes)

private theorem endpoint_mem_He (hu : f.IsInnerUnique)
    {X B : Subgroup G} (hX : IsCartan T L X) (i : Fin 2)
    (hB : B ≤ normalizer (f.Vi i.castSucc : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    endpoint T X B ∈ Chapter1.He G := by
  let P := endpoint T X B
  let U := f.Vi i.castSucc
  have hU : U ≠ ⊥ := f.V_ne_bot i.castSucc
  have hUS : U ≤ commonTwo T X :=
    (D.centralQuotientPreimage_le _).trans (seed_le_commonTwo D S hX)
  have hUP : U ≤ P := hUS.trans (le_sup_left.trans le_sup_right)
  have hPU : P ≤ normalizer (U : Set G) :=
    sup_le hB (sup_le ((commonTwo_le_sylow X).trans (f.invariant i.castSucc))
      (f.cartan_normalizes hu hX i.castSucc))
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf hTB (sylow_normalizes_overlap c hX)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hH : (P ⊔ (T : Subgroup G)) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,fun _ hx => (show (T : Subgroup G) ≤ P ⊔ (T : Subgroup G) from le_sup_right) hx⟩
    intro he
    apply hU
    apply bot_unique
    have hh := le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (hUS.trans (commonTwo_le_sylow X)))
      (hUP.trans (show P ≤ P ⊔ (T : Subgroup G) from le_sup_left))
      (sup_le hPU (f.invariant i.castSucc))
    exact he ▸ hh
  have hn : (P.subgroupOf (P ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hTP)
  exact Chapter1.lemma_1_1_3_1
    (Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T) hH)
    (fun he => hU (bot_unique (he ▸ hUP))) le_sup_left hn.isSubnormal

/-- Both full original endpoints K₀S₀X and L₂S₀X have characteristic two. -/
theorem original_endpoints_characteristic_two (hu : f.IsInnerUnique)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hK₀K : K₀ ≤ K) (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G)) :
    ∀ i, generalizedFitting (endpoint T X (locals K₀ (f.Li 1) i)) =
      pCore 2 (endpoint T X (locals K₀ (f.Li 1) i)) := by
  intro i
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  apply Chapter1.mem_He_iff.mp
  fin_cases i
  · exact endpoint_mem_He D S f hu hX 0 (hK₀K.trans hK.1.1) hTK₀
  · exact endpoint_mem_He D S f hu hX 1 (localResidual_le _ |>.trans inf_le_right)
      (f.sylow_normalizes_Li 1)

omit [Finite G] in
/-- The F.1.1-generated group and the original completion differ exactly by X. -/
theorem completion_eq_generated_sup_cartan (X K₀ L₂ : Subgroup G) :
    completion T X K₀ L₂ =
      ChapterF.Source.generated (locals K₀ L₂) (commonTwo T X) ⊔ X := by
  change (K₀ ⊔ (commonTwo T X ⊔ X)) ⊔ (L₂ ⊔ (commonTwo T X ⊔ X)) =
    ((K₀ ⊔ L₂) ⊔ commonTwo T X) ⊔ X
  ac_rfl

/-- The F.1.1-generated group is relatively normal in the full completion;
the argument uses the action of the original X on each original factor. -/
theorem generated_normalized_by_completion (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    completion T X K₀ (f.Li 1) ≤
      normalizer (ChapterF.Source.generated (locals K₀ (f.Li 1)) (commonTwo T X) : Set G) := by
  rw [completion_eq_generated_sup_cartan]
  apply sup_le (ChapterF.Source.generated _ _).le_normalizer
  have hXK := cartan_normalizes_other_residual D S f hu hm hX hK hLK hK₀ hK₀K hk
  have hXL := cartan_normalizes_flag_residual D S f hu hX 1
  have hXS : X ≤ normalizer (commonTwo T X : Set G) :=
    (le_sup_left : X ≤ X ⊔ (T : Subgroup G)).trans
      ((X ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (le_inf ((le_inf hXK hXL).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)) hXS).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Relative normality carries a trivial core from H to the exact F.1.1 group. -/
theorem generated_core_eq_bot_of_completion_core (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (he : pCore 2 (completion T X K₀ (f.Li 1)) = ⊥) :
    pCore 2 (ChapterF.Source.generated (locals K₀ (f.Li 1)) (commonTwo T X)) = ⊥ := by
  let J := ChapterF.Source.generated (locals K₀ (f.Li 1)) (commonTwo T X)
  have hJH : J ≤ completion T X K₀ (f.Li 1) := by
    rw [completion_eq_generated_sup_cartan]
    exact le_sup_left
  have hh := pCoreIn_mono_of_normalizes (p := 2) hJH
    (generated_normalized_by_completion D S f hu hm hX hK hLK hK₀ hK₀K hk)
  have hz : J.pCoreIn 2 = ⊥ := by
    apply bot_unique
    simpa only [pCoreIn,he,Subgroup.map_bot] using hh
  exact (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz

/-- The literal two-core-free clause of F.1.1 follows from absence of Q.
This does not assert the other F.1.1 clauses or the DGS contradiction. -/
theorem original_generated_core_eq_bot (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hn : ¬ ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G)) :
    pCore 2 (ChapterF.Source.generated (locals K₀ (f.Li 1)) (commonTwo T X)) = ⊥ :=
  generated_core_eq_bot_of_completion_core D S f hu hm hX hK hLK hK₀ hK₀K hk
    (completion_core_eq_bot_of_no_common_normal c hX hTK₀ (f.sylow_normalizes_Li 1) hn)


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
