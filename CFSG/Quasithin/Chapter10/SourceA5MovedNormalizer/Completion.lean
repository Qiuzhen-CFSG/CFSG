module
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OppositeComponent
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.ComponentRanks
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Constrained
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Nonconstrained
/-!
# Source 10.2.6 for the original moved-factor normalizer

Put W=[V,L]. The literal original half-Sylow is Sylow in N_G(W).
A contrary normalizer gives a strict normal component over L; the opposite
original factor is contained in another component, since it centralizes W
and L moves W. Quasithinness bounds the first component's cubic rank by one.
The constrained branch is excluded by the original pushing-up data and C.2.7.
The remaining branch has trivial odd core and is quasisimple; its original
moved A₅ module gives a central quotient of two-rank at least four, forcing
a Bender quotient and contradicting the proper full-Sylow enlargement.

The sole separate-factor premise is actual crossed centralization in the
original module. No point-centralizer containment is used.
Source: Aschbacher--Smith, Lemma 10.2.6, printed pp.748--749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- The full original moved-factor normalizer lies in M, using the separate
factor action and no element-centralizer conclusion. -/
theorem source_a5_moved_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal := by
  let H := normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hH := source_moved_normalizer_sqtk D
  have hXH := source_orbit_le_moved_normalizer D hn
  have hRH := source_join_core_le_moved_normalizer D
  have hSyl := source_a5_moved_normalizer_sylow D e ht htn hcross
  have hHM : H ⊓ D.maximalLocal ≤ normalizer (L : Set G) := by
    rw [inf_comm]
    exact source_original_moved_stabilizer_le_component_normalizer D ht htn hcross
  by_contra hout
  obtain ⟨K,hK,hKN,hLK⟩ := source_a5_moved_normalizer_enlargement D e ht htn hcross hout
  obtain ⟨J,hJ,_,hBJ⟩ := source_a5_moved_normalizer_opposite_component D e ht htn hcross
  have hc := source_a5_moved_normalizer_opposite_cross D ht htn hcross
  have h3 := source_a5_moved_normalizer_component_rank D e hH hK hJ hLK.le hBJ hc (Or.inl rfl)
  have hF := source_a5_moved_normalizer_strict_component_not_constrained D e
    hH hXH hRH hSyl hHM hK hKN hLK h3
  exact source_a5_orbit_overgroup_strict_component_not_nonconstrained D e hn
    hH hXH hRH hSyl hK hLK h3 hF
end CFSG.Quasithin.Chapter10
