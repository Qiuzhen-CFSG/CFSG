module

public import CFSG.Quasithin.Chapter3.Section02.ReducedOrbit

/-!
# The literal actor centralizer in the Fundamental Setup

Centralizing the subgroup represented by an invariant subspace is exactly
pointwise fixation under its original conjugation representation. Apply
D.3.3(2) to this actual kernel, then transport its core–Frattini bound
through the inclusion of the actor into M. This proves the bound for the
original subgroup C_X(V_M), not just an isomorphic action kernel.

Source: Aschbacher–Smith, Lemma 3.2.2(1), combined manuscript of
1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Translate the actual D.3.3 actor kernel back to the original group. -/
theorem reduced_module_actor_centralizer_bound
    (M X : Subgroup G) (hXM : X ≤ M) {S : Sylow 2 M}
    {J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup M))}
    (hi : InternalModuleHypotheses K (ReducedNormal.representation M) S
      (X.subgroupOf M) J) :
    (centralizer (ReducedNormal.subspaceImage M
      (orbitSpan (ReducedNormal.representation M) ⊤ J) : Set G)).subgroupOf X ≤
        coreFrattiniIn X := by
  intro x hx
  let xM : M := ⟨x, hXM x.property⟩
  have hxK : xM ∈ subspaceKernel (ReducedNormal.representation M)
      (orbitSpan (ReducedNormal.representation M) ⊤ J) (X.subgroupOf M) :=
    ⟨x.property, fun v hv => ReducedNormal.representation_fixes_of_centralizes_subspaceImage
      M _ xM hx v hv⟩
  obtain ⟨r, hr, he⟩ := hi.orbit_actorKernel_le_coreFrattini hxK
  rw [← coreFrattiniIn_subgroupOf X M hXM] at hr
  change subgroupOfEquivOfLe hXM r ∈ coreFrattiniIn X at hr
  have her : subgroupOfEquivOfLe hXM r = x :=
    Subtype.ext (congrArg (fun m : M => (m : G)) he)
  rwa [her] at hr

/-- The centralizer conclusion for the original full orbit, retaining
both structural alternatives of 3.2.2. -/
theorem source_reduced_seed_actor_centralizer
    (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
    [(X.subgroupOf M).Normal]
    (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
    (hX : pResidual 2 (X.subgroupOf M) = ⊤)
    (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
      (by rw [normalizer_eq_top]; exact le_top))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
    (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
      (X.subgroupOf (X ⊔ (T : Subgroup G))) I) :
    (centralizer (componentOrbit
      (ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I) M : Set G)).subgroupOf X ≤
        coreFrattiniIn X := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have hb := reduced_module_actor_centralizer_bound M X hXM hi
  have hm := ReducedNormal.subspaceImage_orbitSpan M M le_rfl J
  rw [subgroupOf_self, hJ] at hm
  rwa [hm] at hb

namespace FundamentalSetup
variable {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- C_{L₀}(V_M) lies in the original O₂,Φ(L₀). -/
theorem fullModule_actorCentralizer_le_coreFrattini
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    (centralizer (D.fullModule : Set G)).subgroupOf (localOrbit T L) ≤
      coreFrattiniIn (localOrbit T L) := by
  obtain ⟨J, _, hW, hi⟩ := D.exists_internal_seed h127
  have hb := reduced_module_actor_centralizer_bound D.maximalLocal (localOrbit T L)
    (localOrbit T L).le_normalizer hi
  rwa [hW] at hb

end FundamentalSetup
end CFSG.Quasithin.Chapter3.Section02
