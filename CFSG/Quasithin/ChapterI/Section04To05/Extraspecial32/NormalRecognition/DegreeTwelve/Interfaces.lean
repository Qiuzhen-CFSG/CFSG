module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Intermediate geometry for the degree-twelve construction

The two contracts separate the local fusion and order calculation from the
construction of the eleven-point subgroup. Neither contract is asserted to
follow from the source hypotheses in this module. In particular, the first
contract distinguishes the intersection `Q ∩ Qᵍ` from the canonical fusion
eight, and its order alternative is a conclusion that still needs proof.

The second contract concerns actual subgroups and their literal coset action.
The intersection with the conjugate subgroup is used to identify the other
eleven cosets in the final degree-twelve action. It assumes neither an ambient
permutation action nor an isomorphism with a Mathieu group.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.4, 2.7–2.8 and 4.1–4.11.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open Subgroup

variable {G : Type*} [Group G] {z : G}

/-- The source's conjugate core uses left conjugation throughout. -/
@[expose] public def conjugateCore (z g : G) : Subgroup G :=
  (coreInG z).map (MulAut.conj g).toMonoidHom

/-- The source's `E`, which must not be identified with the fusion eight `F`. -/
@[expose] public def coreIntersection (z g : G) : Subgroup G :=
  coreInG z ⊓ conjugateCore z g

/-- Explicit conclusions of the local analysis, including the reduction using
2.8 and the two order possibilities of 4.3. Their producer must use only
`h`, normality of the quaternion factors, the fusion-eight data, and
nonnormality of that fusion eight. -/
public structure SourceGeometry [Finite G] (h : Hypotheses z) where
  g : G
  fused_mem : g * z * g⁻¹ ∈ coreInG z
  fused_ne : g * z * g⁻¹ ≠ z
  intersection_elementary : IsElementaryAbelian 2 (coreIntersection z g)
  intersection_card : Nat.card (coreIntersection z g) = 8
  intersection_ne_fusion : coreIntersection z g ≠ fusionCore z
  u : G
  u_order : orderOf u = 2
  u_centralizes : u ∈ Centralizer z
  u_conjugate_core : u ∈ conjugateCore z g
  u_not_core : u ∉ coreInG z
  u_fused : IsConj z u
  u_inverts_X : ∀ x : h.X,
    u * ((x : Centralizer z) : G) * u⁻¹ = ((x : Centralizer z) : G)⁻¹
  t : G
  t_mem : t ∈ coreIntersection z g
  t_order : orderOf t = 2
  t_not_fused : ¬ IsConj z t
  involution_classes : ∀ a : G, orderOf a = 2 → IsConj z a ∨ IsConj t a
  order_cases : Nat.card G = 12096 ∨ Nat.card G = 95040

/-- The subgroup configuration at the end of 4.10 and the intersection
calculation in 4.11. Four-transitivity is on the actual left cosets of `L`
inside `M`; it is not a separately supplied abstract permutation action. -/
public structure ElevenSubgroupData (z : G) where
  M : Subgroup G
  L : Subgroup G
  le : L ≤ M
  card_M : Nat.card M = 7920
  card_L : Nat.card L = 720
  z_not_mem : z ∉ M
  intersection : M ⊓ M.map (MulAut.conj z).toMonoidHom = L
  transitive : MulAction.IsMultiplyPretransitive M (M ⧸ L.subgroupOf M) 4

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
