module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinear

/-!
# The literal Chapter 12 application of the linear Cartan analysis

Maximality and nonfaithfulness of the actual residual provide the earlier
5.1.14(1--3) geometry. The two later source branches concern its actual
order-three Cartan subgroup: normalization forces equality of the two
Cartans, and escape is impossible. Their conditional assembly below derives
n = 2 and canonical Borel centralization and applies the existing chosen
module theorem.

The construction of `LinearFieldCartan` and the proofs of both cubic branches
remain separate obligations. No claim of an unconditional 5.1.14 or 12.2.2
is made; chosen T-invariance remains explicit in the module application.
Source: Aschbacher--Smith, 5.1.14--23, pp.638--646; 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- Earlier source geometry on the original chosen setup, including the
centralizer of every nonidentity point, not only the whole omega subgroup. -/
theorem linear_field_source_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    H ≤ omegaCentralizer T ∧
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      ∀ z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
        centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) := by
  have hc := residual_centralizes_omega_of_nonfaithful h.simpleQTKE hH.1.1 hK.1 hnf
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp hc
  exact ⟨hHC, D.centralOmega_disjoint_of_outside_centralizes h hH hHC,
    fun _ hz hne => point_centralizer_le_residual_normalizer h.simpleQTKE
      hH.1.1 hK hnf hz hne⟩

/-- Assembly of the normalizing and escaping cubic branches. Both implications
are retained explicitly until their source owners discharge them. -/
theorem field_four_and_borel_of_linear_cubic_branches
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (c : LinearFieldCartan T L H A B C n)
    (hinside : C ≤ normalizer (residual H : Set G) → A = B)
    (houtside : ¬ C ≤ normalizer (residual H : Set G) → False) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  have hCN : C ≤ normalizer (residual H : Set G) := by
    by_contra hn
    exact houtside hn
  exact c.field_four_and_borel D.sylow_normalizes_component
    (D.linear_field_source_geometry h hH hK hnf).1 (hinside hCN)

/-- The exact selected-module consumer, with both numerical/Borel inputs
derived by the preceding assembly. T-invariance has its independent owner. -/
theorem a5_model_of_linear_cubic_branches
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (c : LinearFieldCartan T L H A B C n)
    (hinside : C ≤ normalizer (residual H : Set G) → A = B)
    (houtside : ¬ C ≤ normalizer (residual H : Set G) → False) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨hn, hB⟩ := D.field_four_and_borel_of_linear_cubic_branches h hH hK hnf
    c hinside houtside
  exact D.a5_model_of_linear_source_borel h hH hK hnf hpsl hn hTV hB

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
