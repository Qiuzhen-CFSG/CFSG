module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.NormalFourSquareFusion
public import Theory.GroupTheory.PGroup.UniqueNormalFourRoots

/-!+# The central-class reduction for a weakly closed normal four

The shared fusion step of Janko–Thompson, Math. Z. 113 (1970), §6,
printed p.395, confines every conjugate of a central involution returning to
the Sylow subgroup to its unique normal four, provided the four is weakly
closed. An outside involution centralizes a square root of the central
involution, by `UniqueNormalFourRoots`. Sylow transport in its centralizer
and the rank bound then give the contradiction, by `NormalFourSquareFusion`.

The result holds without the ambient simplicity, solvability, central-omega
order or quotient-image normality assumptions. In particular it uses neither
normality before quotienting nor an altered quotient image; `fourImage`
retains its definition from `NormalFourOddCoreSetup`.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

/-- Commuting square roots outside the four suffice to confine the conjugacy
class of every central involution. -/
public theorem central_class_mem_four_of_commuting_square_roots
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hweak : ∀ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        E.map (S : Subgroup G).subtype)
    (hroot : ∀ z t : S, z ∈ center S → orderOf z = 2 → orderOf t = 2 →
      t ∉ E → ∃ x : S, x ^ 2 = z ∧ Commute x t) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      IsConj (z : G) (t : G) → t ∈ E := by
  intro z t hzC hz hconj
  by_cases htE : t ∈ E
  · exact htE
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have ht : orderOf t = 2 := by
    calc
      orderOf t = orderOf (t : G) := (orderOf_coe t).symm
      _ = orderOf ((MulAut.conj g) (z : G)) := congrArg orderOf hg.symm
      _ = orderOf (z : G) := (MulAut.conj g).orderOf_eq _
      _ = 2 := (orderOf_coe z).trans hz
  obtain ⟨x, hx, hxt⟩ := hroot z t hzC hz ht htE
  exact S.mem_four_of_isConj_of_commuting_square_root hrank E hE hweak
    z t x hzC hz hconj hx hxt

/-- If the unique normal four is weakly closed, every conjugate of a central
involution returning to the Sylow subgroup belongs to that four. -/
public theorem central_class_mem_four_of_weakly_closed
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hweak : ∀ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        E.map (S : Subgroup G).subtype) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      IsConj (z : G) (t : G) → t ∈ E := by
  apply central_class_mem_four_of_commuting_square_roots hrank S E hE hweak
  exact S.isPGroup'.exists_commuting_square_root_of_unique_normal_four
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE hunique

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
