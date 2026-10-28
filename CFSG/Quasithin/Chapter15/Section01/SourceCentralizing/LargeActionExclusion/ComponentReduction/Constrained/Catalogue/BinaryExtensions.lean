module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGeneration
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions
public import Theory.GroupTheory.NormalSymmetricThreePairExtension

/-!
# The actual Sylow extension of the constrained endpoint parabolic

The generating pair proves that the original S normalizes L, so the source
N_S(L) is exactly S. Adjoining it to the endpoint retains characteristic
two and has literal two-core quotient S₃ × S₃ or S₃ ≀ C₂. The action kernel
is removed by the normal-supplement theorem, not by a splitting assumption.
The original marker and exchanged selection use the same generating pair
and the same quotient marking as BinaryGeneration.

This discharges the endpoint extension calculation used in 15.1.22(3).
Selection of the wreath case when S exchanges the endpoint nodes, exclusion
of A₃ products, and placement in M or M_Z remain with the catalogue owner.
The product case requires the individual minimal parabolics; it is not a
member of the source family solely from this quotient dichotomy. The general
Borel and small-block clauses also remain open.
Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The characteristic-two and quotient clauses on the literal source
extension, with no condition on whether its action exchanges the factors. -/
structure BinaryEndpointExtension (d : CaseIComponentData T M Mc V) (E : Subgroup G) : Prop where
  fitting : generalizedFitting (E ⊔ d.sylowNormalizer : Subgroup G) =
    pCore 2 (E ⊔ d.sylowNormalizer : Subgroup G)
  quotient : Nonempty (((E ⊔ d.sylowNormalizer : Subgroup G) ⧸
        pCore 2 (E ⊔ d.sylowNormalizer : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
    Nonempty (((E ⊔ d.sylowNormalizer : Subgroup G) ⧸
        pCore 2 (E ⊔ d.sylowNormalizer : Subgroup G)) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))

/-- Both invariant generators force normalization of the whole component. -/
theorem BinaryGeneratingParabolics.sylowNormalizer_eq
    {d : CaseIComponentData T M Mc V} {n : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)} (a : d.BinaryGeneratingParabolics e) :
    d.sylowNormalizer = d.S := by
  apply inf_eq_left.mpr
  rw [←a.generated]
  exact (le_inf a.normalizes_interior a.normalizes_endpoint).trans
    (normalizer_inf_normalizer_le_normalizer_sup a.interior a.endpoint)

/-- The actual endpoint has only the product and wreath extensions after
adjoining the original Sylow normalizer and removing its own two-core. -/
theorem BinaryGeneratingParabolics.endpoint_extension
    {d : CaseIComponentData T M Mc V} {n : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)} (a : d.BinaryGeneratingParabolics e) :
    d.BinaryEndpointExtension a.endpoint := by
  have hS : IsPGroup 2 d.sylowNormalizer :=
    T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)
  have hn : d.sylowNormalizer ≤ normalizer (a.endpoint : Set G) :=
    inf_le_left.trans a.normalizes_endpoint
  refine ⟨?_,?_⟩
  · exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_sup_le 2 a.endpoint d.sylowNormalizer
        (a.endpoint_fitting ▸ centralizer_generalizedFitting_le a.endpoint)
        hS hn)
  · obtain ⟨eE⟩ := a.endpoint_quotient
    exact NormalSymmetricThreePairExtension.normalized_join
      a.endpoint d.sylowNormalizer hn eE hS

/-- The original FF marking now supplies the Sylow extension as well as
the actual generating pair and both original flag intersections. -/
theorem PreExclusionSource.constrained_binary_extensions
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t, d.BinaryEndpointExtension a.endpoint := by
  obtain ⟨t,ht,hML,hM,⟨a⟩⟩ :=
    s.constrained_binary_generation (h := h) hG hempty hM hJ hu hf hn e
  exact ⟨t,ht,hML,hM,a,a.endpoint_extension⟩

/-- Exchanged selection retains the same generating pair and literal endpoint
extension on both plane sizes. -/
theorem ExchangedSource.constrained_binary_extensions
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t, d.BinaryEndpointExtension a.endpoint := by
  obtain ⟨t,ht,hML,hM,⟨a⟩⟩ :=
    s.constrained_binary_generation hG hempty hM hJ hu h hf hn e
  exact ⟨t,ht,hML,hM,a,a.endpoint_extension⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The actual marker supplies the endpoint extension on its selected
component, preserving both original primes and the earlier 15.1.14 input. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_extensions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ n : ℕ, n = 4 ∨ n = 5 →
        ∀ e : d.normalizerImage d.L ≃* SL(n,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          ∃ a : d.BinaryGeneratingParabolics t, d.BinaryEndpointExtension a.endpoint) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf _ hn e =>
    s.constrained_binary_extensions (h := h) hG hempty hM hJ hu hf hn e⟩
end CFSG.Quasithin.Chapter15.Section01
