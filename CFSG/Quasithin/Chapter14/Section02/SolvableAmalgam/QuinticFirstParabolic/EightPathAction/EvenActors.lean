module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.CoreMovement
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CentralKernel
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticTwoPathActors

/-!
# The first even extension actor in the original quintic graph

The full Sylow overlap identifies each radius-one kernel with its embedded
two-core. The cubic-core actor from `CoreMovement` therefore transports along
the last edge of every nonbacktracking two-path rooted at true=H. It fixes
the path and induces a four-cycle on the other quintic neighbors. Its actual
consumer is the three-path transitivity theorem in `EightPathAction`.

Only length two is proved here. The Sz(2) quotient is explicit; the D₁₀
exclusion and the remaining even and odd extensions stay with the final
assembly owner qt-e-quintic-sylow-lower.
Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270 and311--312,
in the source configuration of 14.2.20--21, pp.988--989.
-/

public noncomputable section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Section07 SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The first even extension has its actual local order-four actor. -/
theorem source_quintic_two_path_extension_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 2 (base F true), p.Nonbacktracking →
      ∃ a ∈ pathStabilizer F p,
        a^4 ∈ ballKernel F p.endpoint 1 ∧ a^2 ∉ ballKernel F p.endpoint 1 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTL : (T : Subgroup G) ≤ L := hTX.trans le_sup_left
  let SL := T.subtype hTL
  have hSL (i : Bool) : (SL : Subgroup L) ≤ F i := by
    cases i
    · exact fun x hx => hTX hx
    · exact fun x hx => hTH hx
  let S (i : Bool) := SL.subtype (hSL i)
  obtain ⟨hthree, hfive, hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hSi (i : Bool) : ((S i : Subgroup (F i))).map (F i).subtype = F false ⊓ F true := by
    apply map_injective L.subtype_injective
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hSL i)]
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL, hmap]
  have hk (i : Bool) : ballKernel F (base F i) 1 = (F i).pCoreIn 2 :=
    base_kernel_eq_core F i (S i) (hSi i)
  have hXmap : (ballKernel F (base F false) 1).map L.subtype = X.pCoreIn 2 := by
    rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((X.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show X ≤ L from le_sup_left)]
  have hHmap : (ballKernel F (base F true) 1).map L.subtype = H.pCoreIn 2 := by
    rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((H.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]
  have hbase : ∃ a ∈ ballKernel F (base F false) 1,
      a^4 ∈ ballKernel F (base F true) 1 ∧ a^2 ∉ ballKernel F (base F true) 1 := by
    obtain ⟨a, ha, ha4, ha2⟩ := source_suzuki_cubic_core_actor
      hG T hempty hM hu hmany hcard e H hH hi eH
    rw [←hXmap] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨b, hb, ?_, ?_⟩
    · apply (mem_map_iff_mem (f := L.subtype) L.subtype_injective).mp
      rw [hHmap]
      exact ha4
    · intro hh
      apply ha2
      rw [←hHmap]
      exact mem_map_of_mem L.subtype hh
  change ∀ p : BasedWalk (graph F) 2 (base F true), p.Nonbacktracking →
    ∃ a ∈ pathStabilizer F p,
      a^4 ∈ ballKernel F p.endpoint 1 ∧ a^2 ∉ ballKernel F p.endpoint 1
  intro p hp
  exact two_path_kernel_actor F hthree hfive hbase p hp

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
