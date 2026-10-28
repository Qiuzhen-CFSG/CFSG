module

public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Marked inputs to the terminal Thompson calculation

The enlargement is the actual closure of L under E(C_G(t)). A single
isomorphism identifies K⟨z⟩ with S₈, its K with A₈, its L with the pointwise
pair stabilizer A₆, and z with the transposition of that pair. The two Sylow
centralizer conclusions retain their ambient inclusions.

`Prepared` is an intermediate construction to be proved from these inputs:
it selects the Sylow centralizer, places the marked double transposition in
T, and identifies P. It contains no Thompson or rank conclusion and makes no
assertion about centrality of Ω₁(Φ(J(T))).
The parent obstruction task must construct it before using its consumers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma
16.3.11 and the paragraph preceding 16.3.12, printed p.1181 / PDF p.1198.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
open Subgroup
variable {G : Type*} [Group G]

/-- The actual enlargement, not an independent group-family label. -/
def enlargement (t : G) (L : Subgroup G) : Subgroup G :=
  ComponentTransfer.layerClosure (involutionCentralizer t) L

/-- A₆ on the last six of the eight letters, fixing the first pair pointwise. -/
def markedA6 : Subgroup (Equiv.Perm (Fin 8)) :=
  alternatingGroup (Fin 8) ⊓
    (MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 8)) (1 : Fin 8))

/-- The compatible full output of 16.3.11, together with component membership
from the preceding enlargement reduction. Construction belongs to 16.3.9–11. -/
structure MarkedEnlargement (z t : G) (L : Subgroup G) where
  component : IsCentralizerComponent t (enlargement t L)
  equiv : ↥(enlargement t L ⊔ zpowers z) ≃* Equiv.Perm (Fin 8)
  enlargement_image : ((enlargement t L).subgroupOf
    (enlargement t L ⊔ zpowers z)).map equiv.toMonoidHom = alternatingGroup (Fin 8)
  component_image : (L.subgroupOf (enlargement t L ⊔ zpowers z)).map
    equiv.toMonoidHom = markedA6
  involution_image : equiv
    ⟨z, (le_sup_right : zpowers z ≤ enlargement t L ⊔ zpowers z) (mem_zpowers z)⟩ =
      Equiv.swap 0 1
  centralizer_component_sylow :
    ∃ S : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (L : Set G)),
      (S : Subgroup _).map (involutionCentralizer t ⊓ centralizer (L : Set G)).subtype =
        zpowers t ⊔ zpowers z
  centralizer_enlargement_sylow :
    ∃ S : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)),
      (S : Subgroup _).map
        (involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)).subtype = zpowers t

/-- The element denoted `(1,2)(3,4)` in the source, with zero-based letters. -/
noncomputable def MarkedEnlargement.u {z t : G} {L : Subgroup G}
    (d : MarkedEnlargement z t L) : G :=
  (d.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3) : G)

/-- The concrete two-group C₂ × (D₈ wreath C₂). -/
abbrev LocalSylowModel := Multiplicative (ZMod 2) ×
  RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2))

/-- The chosen involution-centralizer Sylow subgroup, viewed in G. -/
def localSylow {t : G} (P : Sylow 2 (involutionCentralizer t)) : Subgroup G :=
  (P : Subgroup _).map (involutionCentralizer t).subtype

/-- Intermediate geometric data after the permitted conjugate of t and the
compatible marking have been selected. Every field is a construction obligation;
none asserts the final contradiction or a Thompson-subgroup calculation. -/
structure Prepared (T : Sylow 2 G) (z t : G) (L : Subgroup G) where
  counterexample : TerminalCounterexample T z L t
  shape : NonterminalCentralizerShape T z L t
  marked : MarkedEnlargement z t L
  centralizer_sylow :
    ∃ S : Sylow 2 ↥(involutionCentralizer t ⊓ involutionCentralizer z),
      (S : Subgroup _).map (involutionCentralizer t ⊓ involutionCentralizer z).subtype =
        (T : Subgroup G) ⊓ involutionCentralizer t
  P : Sylow 2 (involutionCentralizer t)
  centralizer_le : (T : Subgroup G) ⊓ involutionCentralizer t ≤ localSylow P
  u_mem : marked.u ∈ (T : Subgroup G)
  u_centralizes_componentSylow : marked.u ∈ centralizer (componentSylow T L : Set G)
  model : localSylow P ≃* LocalSylowModel
  model_centralFactor : ((zpowers t).subgroupOf (localSylow P)).map model.toMonoidHom =
    (⊤ : Subgroup (Multiplicative (ZMod 2))).prod ⊥
  model_wreathFactor : (((localSylow P ⊓ enlargement t L) ⊔ zpowers z).subgroupOf
    (localSylow P)).map model.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤

variable {z t : G} {L : Subgroup G}

/-- The marked double transposition lies in the actual A₈ enlargement. -/
theorem MarkedEnlargement.u_mem_enlargement (d : MarkedEnlargement z t L) :
    d.u ∈ enlargement t L := by
  have hm : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 ∈
      ((enlargement t L).subgroupOf (enlargement t L ⊔ zpowers z)).map
        d.equiv.toMonoidHom := by
    rw [d.enlargement_image]
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (2 : Fin 8) ≠ 3)]
    decide
  obtain ⟨x, hx, he⟩ := hm
  have hx' : x = d.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3) :=
    d.equiv.injective (he.trans (d.equiv.apply_symm_apply _).symm)
  change ((d.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3)) : G) ∈ enlargement t L
  rw [← hx']
  exact hx

/-- The marked double transposition is an involution. -/
theorem MarkedEnlargement.u_orderOf (d : MarkedEnlargement z t L) : orderOf d.u = 2 := by
  calc
    orderOf d.u = orderOf (d.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3)) :=
      orderOf_coe _
    _ = orderOf (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) := d.equiv.symm.orderOf_eq _
    _ = 2 := orderOf_eq_prime (by decide) (by decide)

/-- The marked double transposition centralizes z. -/
theorem MarkedEnlargement.u_mem_centralizer (d : MarkedEnlargement z t L) :
    d.u ∈ involutionCentralizer z := by
  apply mem_centralizer_singleton_iff.mpr
  let a := d.equiv.symm (Equiv.swap 0 1 * Equiv.swap 2 3)
  let b : ↥(enlargement t L ⊔ zpowers z) :=
    ⟨z, (le_sup_right : zpowers z ≤ enlargement t L ⊔ zpowers z) (mem_zpowers z)⟩
  have h : a * b = b * a := by
    apply d.equiv.injective
    simp only [map_mul, a, b, d.equiv.apply_symm_apply, d.involution_image]
    decide
  exact congrArg Subtype.val h

end CFSG.Quasithin.Chapter16.ThompsonObstruction
