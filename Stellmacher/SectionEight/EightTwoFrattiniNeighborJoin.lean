module
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Theory.GroupTheory.SpecificGroups.OddDihedralFrattiniCore

/-!
# Frattini centralization of a neighbor-center join

In the noncentral local case of (8.2), the Frattini subgroup of any subgroup
X of a vertex two-core Q_d centralizes the neighbor-center join V_d.
No normality of X in either stabilizer is required.

For each neighbor k, (7.3) puts Q_d in G_k. The odd-dihedral quotient of
G_k by Q_k kills the Frattini image of every two-subgroup, so Phi(X) lies
in Q_k. The center Z_k centralizes Q_k; taking the join over all neighbors
proves the claim. The private transport uses the actual inclusion of X
into G_k, preserving its ambient Frattini subgroup.

This is the core-containment transfer used in Stellmacher (8.2), Journal
of Algebra 190 (1997), printed p.38, including its application to V0
intersected with the second backward core. Source:
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext

private theorem ambient_frattini_le_core
    {G : Type*} [Group G] [Finite G] (P X : Subgroup G)
    (hXP : X ≤ P) (hX : IsPGroup 2 X)
    (hD : ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n))) :
    SectionsFiveToSeven.frattiniAmbient X ≤ twoCoreIn P := by
  obtain ⟨n, ⟨model⟩⟩ := hD
  let Y := X.subgroupOf P
  let e : X ≃* Y := (Subgroup.subgroupOfEquivOfLe hXP).symm
  have hY : IsPGroup 2 Y := hX.of_surjective e.toMonoidHom e.surjective
  have hPhi := frattini_two_subgroup_le_twoCore_of_odd_dihedral_quotient
    (3 ^ n) ((by decide : Odd 3).pow) model Y hY
  have hePhi := frattini_le_comap_frattini_of_surjective
    (φ := e.toMonoidHom) e.surjective
  rintro x ⟨y, hy, rfl⟩
  have hyY : e y ∈ frattini Y := hePhi hy
  have hyCore : (e y : P) ∈ pCore 2 P :=
    hPhi (Subgroup.mem_map_of_mem Y.subtype hyY)
  exact Subgroup.mem_map_of_mem P.subtype hyCore

public theorem eight_two_frattini_centralizes_neighbor_join_local
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (d : ctx.Γ.Vertex) (X : Subgroup G) (hX : X ≤ QAt ctx.Γ d) :
    SectionsFiveToSeven.frattiniAmbient X ≤
      Subgroup.centralizer (VAt ctx.Γ d : Set G) := by
  let Γ := ctx.Γ
  have hpQ : IsPGroup 2 (q Γ d) := by
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer Γ d)).map (stabilizer Γ d).subtype
  have hpX : IsPGroup 2 X := hpQ.of_injective
    (Subgroup.inclusion hX) (Subgroup.inclusion_injective hX)
  apply Subgroup.le_centralizer_iff.mpr
  change v Γ d ≤ _
  rw [v, Γ.vAt_def]
  refine sSup_le fun Z hZ => ?_
  obtain ⟨k, hk, rfl⟩ := hZ
  let E : Subgroup G := stabilizer Γ d ⊓ stabilizer Γ k
  let T : Sylow 2 E := default
  have hQG : q Γ d ≤ stabilizer Γ k :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core d k hk T).2.2
  have hPhi : SectionsFiveToSeven.frattiniAmbient X ≤ q Γ k := by
    rw [q, Γ.twoCoreAt_def]
    exact ambient_frattini_le_core (stabilizer Γ k) X (hX.trans hQG) hpX
      (eight_two_dihedral_core_local ctx hcenter k)
  have hkd : d ∈ neighborhood Γ k := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hk))
  exact ((lemma_seven_three ctx.sectionSeven Γ).center_core k d hkd).trans
    ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
      ((SevenSix.centerAmbient_le_centralizer _).trans (Subgroup.centralizer_le hPhi)))

end Stellmacher.SectionEight
