module
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The first two steps in cubic--quintic coset geometry

The ten two-edge paths from a quintic vertex have stabilizers equal to the
local kernel at their cubic middle vertex. The common Sylow and the S₃
quotient identify that kernel with the cubic two-core. Orbit--stabilizer
then gives transitivity, without any order assumption on the common Sylow.
The ambient group and graph may be infinite; only the vertex groups are finite.

Source: the path and local-kernel conventions of Aschbacher--Smith F.3.2--4
and F.7.3, pp.270 and 311--312. Used before recognition in 14.2.20--21.
-/

public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupTheory
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The quintic root is transitive on two-edge nonbacktracking paths. Only
the cubic quotient and the literal common Sylow are used. -/
theorem quintic_two_path_transitive [Finite (F false)] [Finite (F true)]
    (S : Sylow 2 (F false))
    (hS : (S : Subgroup (F false)).map (F false).subtype = F false ⊓ F true)
    (e : (F false ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3))
    (hthree : ((F true).subgroupOf (F false)).index = 3)
    (hfive : ((F false).subgroupOf (F true)).index = 5) :
    RootPathTransitive (graph F) G (base F true) 2 := by
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdeg := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hdeg]; cases v.type <;> decide)
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w h
    have hn := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hcount : Nat.card {p : BasedWalk (graph F) 2 (base F true) //
      p.Nonbacktracking} = 10 := by
    exact BasedWalk.card_nonbacktracking_succ (graph F)
      (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hflip hdeg 1 (base F true)
  have : Finite {p : BasedWalk (graph F) 2 (base F true) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [hcount]; decide)
  have hedge : (graph F).Adj (base F true) (base F false) :=
    ⟨(by change true ≠ false; decide), incident_base F true false⟩
  obtain ⟨c, hc, hcne⟩ := Set.exists_ne_of_one_lt_ncard
    (show 1 < ((graph F).neighborSet (base F false)).ncard by
      change 1 < Nat.card ((graph F).neighborSet (base F false))
      rw [hdeg]; change 1 < 3; decide) (base F true)
  let p : BasedWalk (graph F) 2 (base F true) :=
    ⟨⟨base F false, hedge⟩, ⟨⟨c, hc⟩, PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hcne, trivial⟩
  have hSloc : ((F false ⊓ F true).subgroupOf (F false)) = (S : Subgroup (F false)) := by
    apply map_injective (F false).subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_left, hS]
  have hcore : ((F false ⊓ F true).subgroupOf (F false)).normalCore = pCore 2 (F false) := by
    rw [hSloc]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, S.isPGroup'.to_le (S : Subgroup (F false)).normalCore_le⟩
    · exact normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal S)
  have hk : ballKernel F (base F false) 1 = (pCore 2 (F false)).map (F false).subtype := by
    have hh := congrArg (map (F false).subtype) (base_ballKernel_one F false)
    rw [map_subgroupOf_eq_of_le (show ballKernel F (base F false) 1 ≤ F false by
      simpa only [stabilizer, stabilizer_base] using ballKernel_le_stabilizer F (base F false) 1),
      hcore] at hh
    exact hh
  have hfix : Nat.card (pathStabilizer F p) = Nat.card (pCore 2 (F false)) := by
    rw [pathStabilizer_two_eq_ballKernel_one F p hp (hdeg (base F false)), hk]
    exact card_map_of_injective (F false).subtype_injective
  have hcommon : Nat.card (F false ⊓ F true : Subgroup G) = 2 * Nat.card (pCore 2 (F false)) := by
    have hs := (S : Subgroup (F false)).index_mul_card
    rw [SymmetricThreeTwoCore.sylow_index_three e S, SymmetricThreeTwoCore.card_eq e] at hs
    have hm := card_map_of_injective (K := (S : Subgroup (F false))) (F false).subtype_injective
    rw [hS] at hm
    omega
  have htrue := ((F false).subgroupOf (F true)).index_mul_card
  rw [hfive, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (show F false ⊓ F true ≤ F true from inf_le_right)).toEquiv,
    hcommon] at htrue
  have : Finite (stabilizer F (base F true)) := by
    rw [stabilizer, stabilizer_base]
    infer_instance
  apply rootPathTransitive_of_pathStabilizer_card_le F p hp
    (Nat.card_pos : 0 < Nat.card (pCore 2 (F false))) hfix.le
  rw [stabilizer, stabilizer_base, hcount]
  omega
end Subgroup.CosetGeometry.RankTwo
