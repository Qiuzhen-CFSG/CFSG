module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Interfaces
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Marked local inputs to the eleven-point subgroup

These are intermediate contracts, not assertions that the local hypotheses
already supply the indicated subgroups. `SymmetricSixData` records the
commuting cubic subgroup and the actual marked symmetric-group isomorphism
from Lemmas 4.5–4.6. `MarkedLocalData` records the particular consequences of
the normalizer calculation needed to construct the eleven-point subgroup.
Its three-transitive action is on the literal quotient of the marked subgroup
of order 720 by its subgroup of order 72.

The consumer constructs `M = L ∪ LvL`, proves closure, computes its order,
and raises three-transitivity to four-transitivity. Neither this subgroup
nor its action is a field of either input. The two braid relations also
prove the strictness needed for the intersection calculation in 4.11.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 4.5–4.10, especially pp.40–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup DoubleCoset

variable {G : Type*} [Group G] {z : G}

/-- The chosen cubic subgroup in the ambient group, with the source embedding. -/
@[expose] public def cubicInG [Finite G] (h : Hypotheses z) : Subgroup G :=
  (h.X : Subgroup (Centralizer z)).map (Centralizer z).subtype

/-- The marked construction in 4.5–4.6. Replacing the source involution `u`
by `uz` is permitted, but the resulting involution and the actual isomorphism
with `S₆` are recorded. The centralizer order is the last observation of 4.5,
used later in 4.9. -/
public structure SymmetricSixData [Finite G] (h : Hypotheses z) (a : SourceGeometry h) where
  u : G
  u_choice : u = a.u ∨ u = a.u * z
  u_order : orderOf u = 2
  u_fused : IsConj z u
  X1 : Subgroup G
  card_X1 : Nat.card X1 = 3
  X1_centralizes_X : X1 ≤ centralizer (cubicInG h : Set G)
  z_inverts_X1 : ∀ x ∈ X1, z * x * z⁻¹ = x⁻¹
  u_centralizes_X1 : ∀ x ∈ X1, u * x = x * u
  centralizer_X_card : Nat.card (centralizer (cubicInG h : Set G)) = 18 ∨
    Nat.card (centralizer (cubicInG h : Set G)) = 54
  S : Subgroup G
  generated : S = fusionCore z ⊔ fusionCore u ⊔ cubicInG h ⊔ X1
  equiv : S ≃* Equiv.Perm (Fin 6)
  z_mem : z ∈ S
  u_mem : u ∈ S
  z_swap : (equiv ⟨z, z_mem⟩).IsSwap
  u_swap : (equiv ⟨u, u_mem⟩).IsSwap

/-- The specific marked consequences of 4.8–4.10 used in the final subgroup
construction. In the source `K = N_L(D)`. The element `r` is chosen in `L`
so that `L = K ∪ KrK` and `vrv = rvr`; `v` normalizes `K` and lies outside
`L`. The last two fields use the source's distinguished involution `z`.
Constructing this input still requires the actual local normalizer analysis. -/
public structure MarkedLocalData (z : G) where
  L : Subgroup G
  K : Subgroup G
  le : K ≤ L
  card_L : Nat.card L = 720
  card_K : Nat.card K = 72
  transitive : MulAction.IsMultiplyPretransitive L (L ⧸ K.subgroupOf L) 3
  v : G
  v_sq : v * v = 1
  v_not_mem : v ∉ L
  v_normalizes : v ∈ normalizer (K : Set G)
  r : G
  r_mem : r ∈ L
  cover : ∀ l ∈ L, l ∈ K ∨ l ∈ doubleCoset r K K
  braid : v * r * v = r * v * r
  z_normalizes : z ∈ normalizer (L : Set G)
  z_not_mem : z ∉ L
  vz_cube : (v * z) ^ 3 = 1

/-- The actual symmetric subgroup excludes the order-12096 alternative of
4.3, giving the selection used in 4.7 and the later normalizer calculation. -/
public theorem SymmetricSixData.ambient_card [Finite G] {h : Hypotheses z}
    {a : SourceGeometry h} (s : SymmetricSixData h a) : Nat.card G = 95040 := by
  have hs : Nat.card s.S = 720 := by
    rw [Nat.card_congr s.equiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  rcases a.order_cases with hc | hc
  · have hd := s.S.card_subgroup_dvd_card
    rw [hs, hc] at hd
    norm_num at hd
  · exact hc

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
