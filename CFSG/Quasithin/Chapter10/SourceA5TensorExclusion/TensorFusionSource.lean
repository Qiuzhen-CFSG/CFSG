module
public import CFSG.Quasithin.Chapter10.SourceFullModuleFusion
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCenterFree

/-!
# Fusion on the original determinant tensor module

The determinant action is not an FF-module, so J(T) centralizes the
original full module. Subgroup and element fusion are consequently
controlled by M. The same Thompson argument upgrades the local Sylow
centralizer of a tensor vector to its ambient centralizer.

These are the original 3.2.10 inputs used in 9.4.1--5, with Thompson
centralization discharged by the actual tensor marking.
Source: Aschbacher--Smith, printed pp.583 and 735--737.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem tensor_subgroup_fusion {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (g : G) (hg : U.map (MulAut.conj g).toMonoidHom ≤ D.fullModule) :
    ∃ n ∈ D.maximalLocal,
      U.map (MulAut.conj n).toMonoidHom = U.map (MulAut.conj g).toMonoidHom :=
  source_fullModule_subgroup_fusion D m.thompson_centralizes_fullModule hUV g hg

theorem tensor_element_fusion {x y : G}
    (hx : x ∈ D.fullModule) (hy : y ∈ D.fullModule) (hxy : IsConj x y) :
    ∃ n ∈ D.maximalLocal, n * x * n⁻¹ = y :=
  source_fullModule_element_fusion D m.thompson_centralizes_fullModule hx hy hxy

theorem tensor_conjugate_through {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ normalizer (U : Set G),
      D.fullModule.map (MulAut.conj c).toMonoidHom =
        D.fullModule.map (MulAut.conj g).toMonoidHom :=
  source_fullModule_conjugate_through D m.thompson_centralizes_fullModule hUV g hg

theorem tensor_unique_conjugate {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hn : normalizer (U : Set G) ≤ D.maximalLocal)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
  source_fullModule_unique_conjugate D m.thompson_centralizes_fullModule hUV hn g hg

theorem tensor_centralizer_sylow {v : G} (hv : v ∈ D.fullModule)
    (hS : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) := by
  apply source_sylow_in_of_thompson_le D m.thompson_centralizes_fullModule _ _ _ hS
  exact le_inf (sSup_le fun _ h => h.1)
    (m.thompson_centralizes_fullModule.trans
      (centralizer_le (Set.singleton_subset_iff.mpr hv)))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
