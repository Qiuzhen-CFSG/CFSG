module

public import CFSG.Quasithin.Chapter13.Section07.FittingOffenders
public import CFSG.Quasithin.Chapter13.Section07.PlusOffenders

/-!
# Constructing the original Fitting-centralizing offender

The original marked conjugator and plus action are constructed by13.7.12.
The genuine earlier13.7.4 assertion C_H(U_H/U₀)=O₂(H) makes that action
faithful via its proved literal kernel. Minimizing a best offender in A*
and applying13.7.14 gives the actual offender used to select a component.

Source: Aschbacher–Smith13.7.14 and the following paragraph, printed p.943.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

omit [Finite G] d in
/-- The actual descended action is faithful from the earlier source kernel equality. -/
theorem source_plus_faithful_of_kernel_eq
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    Function.Injective σ := by
  let π := QuotientGroup.mk' (pCore 2 H)
  have he : (σ.comp π).ker = pCore 2 H := map_injective H.subtype_injective
    ((PlusAction.section_action_kernel s).trans hk)
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  have ha : a ∈ (σ.comp π).ker := hx
  rw [he] at ha
  exact (QuotientGroup.eq_one_iff a).mpr ha

include d in
/-- The selected original minimal offender centralizes F(H*). Faithfulness
is supplied solely by the original13.7.4 kernel equality. -/
theorem exists_source_fitting_centralizing_offender
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      let U := Section08.Source.UH H V₃
      let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
      let π := QuotientGroup.mk' (pCore 2 H)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ U₀.subgroupOf U)))
          (s : Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (B : Subgroup (H ⧸ pCore 2 H)),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧
          B ≤ (A.subgroupOf H).map π ∧
          B ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) ∧
          Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
          subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ := by
  obtain ⟨g,hs,hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g : G) hspan hU hV
  obtain ⟨hE,σ,s,sQ,hpair,hcoord,hA,hUg⟩ :=
    source_plus_offenders d h hU hV (inclusion le_sup_left g) hs hout
  let := hE
  have hf := source_plus_faithful_of_kernel_eq σ s hk
  obtain ⟨C,hCA,hC⟩ := hA.exists_bestOffender σ
  obtain ⟨B,hB,hBC⟩ := hC.exists_minimal σ
  have hBA := hBC.1.trans hCA
  exact ⟨g,hs,hspan,hout,hE,σ,s,B,hf,hB,hBA,
    source_minimal_offender_centralizes_fitting d h hU hV hne
      (inclusion le_sup_left g) hs hout σ s hf hB hBA,
    source_plus_seed_plane d h hU hV hne (inclusion le_sup_left g) hs hout σ s B hBA⟩

end CFSG.Quasithin.Chapter13.Section07
