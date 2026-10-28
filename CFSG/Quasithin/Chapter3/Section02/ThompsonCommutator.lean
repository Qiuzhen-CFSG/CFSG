module

public import CFSG.Quasithin.ChapterD.Section03.ActorCommutator
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction

/-!
# The original FSU Thompson commutator

The source's moving-Thompson branch gives a nontrivial action of the
literal J(T) on V. The faithful local orbit image and its core–Frattini
kernel then prove L₀=[L₀,J(T)]. The original internal conjugation image
on V is an FF-module by the already proved maximal-elementary argument.

These discharge the algebraic implications in 3.2.2(6). The earlier
Baumann alternative 3.1.7–8 is still needed to force J(T) to move V
from C_{V_M}(L₀) nontrivial and uniqueness.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open Stellmacher ChapterD.Section03
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

theorem actor_eq_commutator_of_thompson_not_centralizes
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let J := elementaryAbelianMaxJ (S : Subgroup H)
  let ρ := ReducedNormal.representation H
  let W := orbitSpan ρ ⊤ D.seedSpace
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ D.seedSpace)
  have hjmap : J.map H.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hJT : J ≤ (S : Subgroup H) := sSup_le fun _ hA => hA.1
  have hTJ : (S : Subgroup H) ≤ normalizer (J : Set H) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (elementaryAbelianMaxJ (S : Subgroup H)).map (MulAut.conj t).toMonoidHom = _
    have hs : (S : Subgroup H).map (MulAut.conj t).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup H).le_normalizer ht)
    rw [← elementaryAbelianMaxJ_map_equiv, hs]
  have hjker : ¬ J ≤ f.ker := by
    intro hj
    apply hJ
    rw [← hjmap]
    rintro _ ⟨g, hg, rfl⟩ v hv
    have hfix := hj hg
    rw [invariantActionHom_ker] at hfix
    rw [← D.local_orbitImage_eq_module] at hv
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
    have he := congrArg (fun z : Additive (ReducedNormal.ModuleGroup H) => z.toMul.val.val)
      (hfix.2 (Additive.ofMul w) hw)
    change (g : G) * w.val.val * (g : G)⁻¹ = w.val.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hgen : X ⊔ (S : Subgroup H) = ⊤ := by
    change (localOrbit T L).subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hi := D.local_internal_module h127
  have he := hi.actor_eq_commutator_of_moving_twoGroup hgen hJT hTJ hjker
  have hm := congrArg (map H.subtype) he
  change X.map H.subtype = (⁅X, J⁆).map H.subtype at hm
  have hXM : X.map H.subtype = localOrbit T L := map_subgroupOf_eq_of_le le_sup_left
  rw [map_commutator, hXM, hjmap] at hm
  exact hm

/-- Both algebraic conclusions of 3.2.2(6) follow from the actual
moving-Thompson alternative of the earlier source theorem. -/
theorem thompson_movement_consequences
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    letI := D.module_elementary
    localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module) := by
  let := D.module_elementary
  exact ⟨D.actor_eq_commutator_of_thompson_not_centralizes h127 hJ,
    D.module_isFF_of_thompson_not_centralizes hJ⟩

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
