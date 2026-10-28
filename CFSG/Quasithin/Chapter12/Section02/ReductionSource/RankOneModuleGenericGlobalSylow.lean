module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalNormalizer

/-!
# The common Sylow in the Chapter12 generic pair

Apply the concrete catalogue to the actually selected whole-residual pair.
Every ordinary row gives S = T ∩ L = T ∩ O²(H) and the two identities
O₂(GᵢT) = O₂(Lᵢ). These discharge the corresponding premises of the
normalizer calculation and give its local conditions on the full overlap.
The degree-two unitary extension is retained with both amalgam maps.
Its parity calculation now proves T ∩ L = T ∩ O²(H) as well. The
normalizer application therefore uses this reduced common Sylow in every
row. The full-overlap diagonal calculation now also supplies both enlarged
core identities, removing that explicit premise in the final application.

The independent original uniqueness input, exhaustive comparison, and
right-factor maximality from 5.2.8 remain explicit. Identifying the reduced
unitary subamalgam and the ambient completion remains
with the generic/global owner; this
application does not establish GlobalExit. The original uniqueness producer
is qt-d-1222-rankone-global-uniqueness.
Source: Aschbacher–Smith 5.2.6–8 and 5.3.1–2, printed pp.650–653,658–659,
and the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual ordinary pair now supplies its common Sylow and enlarged
cores. The extension branch keeps its original concrete compatible maps,
so its different Sylow convention is not silently replaced by sourceS. -/
theorem rankOne_global_normalizer_geometry_or_unitaryExtension
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      (((∀ i : Fin 2, Global.sourceS L H = (T : Subgroup G) ⊓ ![L,residual H] i) ∧
        (∀ i : Fin 2,
          (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊔
            (T : Subgroup G)).pCoreIn 2 = (![L,residual H] i).pCoreIn 2) ∧
        Chapter5.Section03GreenExtension.SourceLocalConditions
          (Global.normalizerAmalgam L (residual H)) L (residual H) (Global.sourceS L H)) ∨
      ∃ (m : ℕ) (hm : 1 < m),
        Nonempty (RankTwoAmalgam.Iso
          (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
          (ChapterF.GreenBook.LieModels.UnitaryFour.Extension.amalgam m hm.le)) ∨
        Nonempty (RankTwoAmalgam.Iso
          (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
          (ChapterF.GreenBook.LieModels.UnitaryFour.Extension.amalgam m hm.le).reverse)) := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  refine ⟨A,B,d,?_⟩
  rcases d.sourceS_le_factors_or_unitaryExtension hi hH.1.1.2 hp
      (hcomparison A B (residual H) d hp) with hs | he
  · obtain ⟨hs,hc⟩ := d.ordinary_sylow_core_geometry hi hH.1.1.2 hs
    exact Or.inl ⟨hs,hc,d.normalizer_local_conditions hi hH hK (hs 0) (hs 1) hc⟩
  · exact Or.inr he


/-- Source 5.2.7's common Sylow on the actual Chapter12 pair, including the
unitary extension. The parity calculation uses the compatible comparison maps;
no common-Sylow or right-maximality premise is added. -/
theorem rankOne_global_common_sylow_of_concrete_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)))
    : (T : Subgroup G) ⊓ L = (T : Subgroup G) ⊓ residual H := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  exact d.common_sylow_of_comparison (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp (hcomparison A B (residual H) d hp)

/-- Discharge both common-Sylow premises in the original normalizer argument
also in the unitary extension. The remaining enlarged-core and right-maximality
conclusions of 5.2.7--8 are explicit, as are classification and uniqueness. -/
theorem rankOne_global_normalizer_local_conditions_of_concrete_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hc : ∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊔
        (T : Subgroup G)).pCoreIn 2 = (![L,residual H] i).pCoreIn 2) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hs := d.common_sylow_of_comparison hi hH.1.1.2 hp
    (hcomparison A B (residual H) d hp)
  exact ⟨A,B,d,d.normalizer_local_conditions hi hH hK rfl hs hc⟩

/-- The concrete comparisons now discharge both common-Sylow premises and
both enlarged-core premises of the original normalizer argument. This includes
the degree-two unitary row without replacing sourceS by the reduced Sylow.
Exhaustive comparison, original uniqueness, and 5.2.8 right maximality remain
explicit source inputs. -/
theorem rankOne_global_normalizer_geometry_of_concrete_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hs := d.common_sylow_of_comparison hi hH.1.1.2 hp
    (hcomparison A B (residual H) d hp)
  have hc := d.parabolic_sylow_core_eq_of_comparison hi hH.1.1.2 hp
    (hcomparison A B (residual H) d hp)
  exact ⟨A,B,d,d.normalizer_local_conditions hi hH hK rfl hs hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
