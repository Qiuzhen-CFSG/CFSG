module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# D-systems of type A₃ and C₃

The local data in Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.5, printed pp. 418–419 (combined manuscript, 1 March 2004).

Parabolics are specified in the subgroup lattice: over the fixed Sylow
2-subgroup, the two distinct maximal proper overgroups are exactly the
specified pairwise intersections. For the rank-two groups over F₂ appearing
here, these are the rank-one parabolics. No incidence, connectivity, action
kernel, or graph-count conclusion is included in this interface.

Only the vertex groups are required to be finite; the generated ambient group
is not assumed finite. All core and residual subgroups are formed intrinsically
in the indicated intersection before mapping to the ambient group.
-/

@[expose] public section

namespace Quasithin.I5

/-- The two diagrams occurring in I.5. -/
inductive Diagram where
  | A3
  | C3
  deriving DecidableEq

variable {G : Type*} [Group G]

/-- The intersection `G_J`; the empty intersection is the ambient group. -/
def intersection (F : Fin 3 → Subgroup G) (J : Set (Fin 3)) : Subgroup G :=
  ⨅ j ∈ J, F j

/-- The chamber subgroup `T = G₀ ∩ G₁ ∩ G₂`. -/
def chamberSubgroup (F : Fin 3 → Subgroup G) : Subgroup G := ⨅ i, F i

/-- The core `Q_J = O₂(G_J)` in the ambient group. -/
def core (F : Fin 3 → Subgroup G) (J : Set (Fin 3)) : Subgroup G :=
  (intersection F J).pCoreIn 2

/-- The residual `L_J = O²(G_J)` in the ambient group. -/
noncomputable def residual (F : Fin 3 → Subgroup G) (J : Set (Fin 3)) : Subgroup G :=
  (sInf {N : Subgroup (intersection F J) | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}).map
    (intersection F J).subtype

/-- An intrinsic pairwise intersection in the vertex group `Gᵢ`. -/
def localParabolic (F : Fin 3 → Subgroup G) (i j : Fin 3) : Subgroup (F i) :=
  (F j).subgroupOf (F i)

/-- The subgroup-lattice description of the rank-one parabolics in rank two.
The fixed Borel is a Sylow 2-subgroup for the local groups over F₂. -/
structure RankTwoParabolics (H : Type*) [Group H] (B P R : Subgroup H) : Prop where
  left_maximal : IsCoatom P
  right_maximal : IsCoatom R
  distinct : P ≠ R
  borel_eq : P ⊓ R = B
  exhaustive : ∀ U : Subgroup H, B ≤ U → IsCoatom U → U = P ∨ U = R

/-- The two rank-one parabolics generate the local group. -/
theorem RankTwoParabolics.generate {H : Type*} [Group H] {B P R : Subgroup H}
    (h : RankTwoParabolics H B P R) : P ⊔ R = ⊤ :=
  h.left_maximal.sup_eq_top_of_ne h.right_maximal h.distinct

/-- A source D-system. The fields are D1–D5 and local finiteness. -/
structure DSystem (D : Diagram) (G : Type*) [Group G] where
  family : Fin 3 → Subgroup G
  finite_vertex : ∀ i, Finite (family i)
  point_A3 : D = .A3 → Nonempty
    ((family 0 ⧸ pCore 2 (family 0)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
  point_C3 : D = .C3 →
    Nonempty ((family 0 ⧸ pCore 2 (family 0)) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((family 0 ⧸ pCore 2 (family 0)) ≃* Equiv.Perm (Fin 6))
  line_quotient : Nonempty ((family 1 ⧸ pCore 2 (family 1)) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  plane_quotient : Nonempty ((family 2 ⧸ pCore 2 (family 2)) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
  sylow : ∀ i, ∃ S : Sylow 2 (family i),
    (S : Subgroup (family i)) = (chamberSubgroup family).subgroupOf (family i)
  point_parabolics : RankTwoParabolics (family 0)
    ((chamberSubgroup family).subgroupOf (family 0))
    (localParabolic family 0 1) (localParabolic family 0 2)
  line_parabolics : RankTwoParabolics (family 1)
    ((chamberSubgroup family).subgroupOf (family 1))
    (localParabolic family 1 0) (localParabolic family 1 2)
  plane_parabolics : RankTwoParabolics (family 2)
    ((chamberSubgroup family).subgroupOf (family 2))
    (localParabolic family 2 0) (localParabolic family 2 1)
  generate : (⨆ i, family i) = ⊤
  core_free : (chamberSubgroup family).normalCore = ⊥
  nondegenerate : D = .C3 →
    Subgroup.center (family 0) ≠ ⊥ ∨ 32 < Nat.card (pCore 2 (family 0))

namespace DSystem

variable {D : Diagram} (S : DSystem D G)

instance (i : Fin 3) : Finite (S.family i) := S.finite_vertex i

/-- The common Sylow subgroup. -/
abbrev T : Subgroup G := chamberSubgroup S.family

/-- The vertex core in the ambient group. -/
abbrev Q (i : Fin 3) : Subgroup G := (S.family i).pCoreIn 2

/-- The stabilizer of the standard pair of types `i,j`. -/
abbrev pair (i j : Fin 3) : Subgroup G := S.family i ⊓ S.family j

theorem T_le (i : Fin 3) : S.T ≤ S.family i := iInf_le _ i

theorem Q_le_T (i : Fin 3) : S.Q i ≤ S.T := by
  obtain ⟨P, hP⟩ := S.sylow i
  have h := (S.family i).pCoreIn_le_sylow P
  rw [hP, Subgroup.map_subgroupOf_eq_of_le (S.T_le i)] at h
  exact h

theorem T_isTwoGroup : IsPGroup 2 S.T := by
  obtain ⟨P, hP⟩ := S.sylow 0
  have h := P.isPGroup'.map (S.family 0).subtype
  rwa [hP, Subgroup.map_subgroupOf_eq_of_le (S.T_le 0)] at h

/-- The chamber core within a vertex group is precisely its two-core. -/
theorem local_normalCore (i : Fin 3) :
    ((S.T).subgroupOf (S.family i)).normalCore = pCore 2 (S.family i) := by
  obtain ⟨P, hP⟩ := S.sylow i
  rw [← hP]
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, P.isPGroup'.to_le (P : Subgroup (S.family i)).normalCore_le⟩
  · exact Subgroup.normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal P)

/-- A normal subgroup lying in the chamber is trivial (D4). -/
theorem normal_eq_bot (N : Subgroup G) [N.Normal] (hN : N ≤ S.T) : N = ⊥ := by
  apply le_bot_iff.mp
  rw [← S.core_free]
  exact Subgroup.normal_le_normalCore.mpr hN

/-- Each vertex core is normalized by its vertex group. -/
theorem family_le_normalizer_Q (i : Fin 3) :
    S.family i ≤ Subgroup.normalizer (S.Q i : Set G) := by
  have h := (pCore 2 (S.family i)).le_normalizer_map (S.family i).subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, Q, Subgroup.pCoreIn] using h

/-- The core of either vertex group lies in the core of the pair stabilizer. -/
theorem Q_le_pair_core (i j : Fin 3) : S.Q i ≤ (S.pair i j).pCoreIn 2 := by
  apply Subgroup.le_pCoreIn_of_normalizes ((S.family i).isPGroup_pCoreIn 2)
  · exact le_inf ((S.family i).pCoreIn_le 2) ((S.Q_le_T i).trans (S.T_le j))
  · exact inf_le_left.trans (S.family_le_normalizer_Q i)

/-- The easy inclusion of I.5.7(1), before the local quotient analysis. -/
theorem Q_sup_Q_le_pair_core (i j : Fin 3) :
    S.Q i ⊔ S.Q j ≤ (S.pair i j).pCoreIn 2 := by
  refine sup_le (S.Q_le_pair_core i j) ?_
  simpa only [pair, inf_comm] using S.Q_le_pair_core j i

/-- The two standard parabolics generate the point stabilizer. -/
theorem point_parabolics_generate :
    localParabolic S.family 0 1 ⊔ localParabolic S.family 0 2 = ⊤ :=
  S.point_parabolics.generate

/-- The two standard parabolics generate the line stabilizer. -/
theorem line_parabolics_generate :
    localParabolic S.family 1 0 ⊔ localParabolic S.family 1 2 = ⊤ :=
  S.line_parabolics.generate

/-- The two standard parabolics generate the plane stabilizer. -/
theorem plane_parabolics_generate :
    localParabolic S.family 2 0 ⊔ localParabolic S.family 2 1 = ⊤ :=
  S.plane_parabolics.generate

end DSystem
end Quasithin.I5
