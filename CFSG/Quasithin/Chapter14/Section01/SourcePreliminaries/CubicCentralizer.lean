module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ExceptionalFactors
public import Theory.SpecificGroups.Alternating.CubicOrbitOmegaCentralizer

/-!
# The central seed centralizer in an exceptional cubic orbit

A normal A₄ or A₄² orbit product and its centralizer generate the local group
with its Sylow two-subgroup. The intrinsic cubic involution argument bounds
the centralizer of the Sylow omega-center. Unique placement of the ambient
central seed centralizer transfers that bound into the local group.

Source: Aschbacher–Smith 14.1.13, printed p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

theorem source_cubic_orbit_centralizer_control
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (he : M = Mc) (N : Subgroup M) [N.Normal]
    (hm : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    centralizer (centralInvolutions T : Set G) ≤
      (centralizer (N : Set M) ⊔ (T.subtype hTM : Subgroup M)).map M.subtype := by
  have hgen : (N ⊔ centralizer (N : Set M)) ⊔ (T.subtype hTM : Subgroup M) = ⊤ :=
    normal_centralizer_sup_sylow_eq_top N (T.subtype hTM)
      (AlternatingThree.cubic_model_structure N hm).2.2
  have hc := CubicOrbit.centralizer_omega_le_of_normal_cubic N (T.subtype hTM) hm hgen
  have hZM : (omegaOneCenterAmbient (T.subtype hTM : Subgroup M)).map M.subtype =
      centralInvolutions T := by
    rw [←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
    rfl
  have hCM : centralizer (centralInvolutions T : Set G) ≤ M := by
    rw [he]
    exact (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  intro g hg
  refine ⟨⟨g,hCM hg⟩,hc ?_,rfl⟩
  intro z hz
  apply Subtype.ext
  exact hg z (hZM ▸ mem_map_of_mem M.subtype hz)

end CFSG.Quasithin.Chapter14.SourcePreliminaries
