module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocalData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightActionCore
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Odd-action input for the local splitting

The moving plane lies in the elementary closure. An outside conjugate
involution normalizes its centralizer and inverts an odd-order automorphism
of that centralizer. The automorphism acts without nonidentity fixed points
on the plane, fixes the selected noncentral involution, and moves the central
involution. The outside involution has fixed subgroup of index two and acts
nontrivially on the plane.

These are the geometric inputs to the fixed-factor argument: the plane and
the outside involution's fixed subgroup cover the centralizer, so the outside
involution acts trivially modulo the plane. The inverted odd automorphism
then also acts trivially on that quotient, and its fixed subgroup complements
the plane. Existence of the data below remains a separate assertion.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388,
from the order-six automizer through the construction of the odd element r.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The closure centralizer on which the lifted odd element acts. -/
public abbrev closureCentralizer {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) : Subgroup S :=
  centralizer (closureInSylow d : Set S)

/-- A geometric odd actor, before constructing its complementary fixed factor. -/
public structure OddActionData
    {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) (z : S) where
  plane : Subgroup S
  plane_elementary : IsElementaryAbelian 2 plane
  plane_card : Nat.card plane = 4
  plane_le : plane ≤ closureInSylow d
  plane_normalized : centralizer ({i} : Set S) ≤ normalizer (plane : Set S)
  index : (closureCentralizer d).relIndex (centralizer ({i} : Set S)) = 2
  mover : S
  mover_outside : mover ∉ centralizer ({i} : Set S)
  outside : S
  outside_mem_conjugate : outside ∈
    (closureInSylow d).map (MulAut.conj mover).toMonoidHom
  outside_order : orderOf outside = 2
  outside_not_centralizing : outside ∉ closureCentralizer d
  outside_mem_centralizer : outside ∈ centralizer ({i} : Set S)
  outside_normalizes : outside ∈ normalizer (closureCentralizer d : Set S)
  outside_fixed_index : (MulAut.fixedSubgroup
    ((closureCentralizer d).normalizerMonoidHom ⟨outside, outside_normalizes⟩)).index = 2
  outside_moves_plane : ∃ a ∈ plane, ¬ Commute outside a
  actor : MulAut (closureCentralizer d)
  actor_odd : Odd (orderOf actor)
  actor_plane_stable : ∀ a : closureCentralizer d,
    (a : S) ∈ plane → (actor a : S) ∈ plane
  actor_plane_free : ∀ a : closureCentralizer d,
    (a : S) ∈ plane → actor a = a → a = 1
  actor_inverted :
    (closureCentralizer d).normalizerMonoidHom ⟨outside, outside_normalizes⟩ * actor *
      ((closureCentralizer d).normalizerMonoidHom ⟨outside, outside_normalizes⟩)⁻¹ = actor⁻¹
  involution_mem : i ∈ closureCentralizer d
  central_mem : z ∈ closureCentralizer d
  actor_fixes_involution : actor ⟨i, involution_mem⟩ = ⟨i, involution_mem⟩
  actor_moves_central : actor ⟨z, central_mem⟩ ≠ ⟨z, central_mem⟩

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
