module

public import Theory.GroupTheory.SolvableCentralFour
public import Theory.GroupTheory.TwoSubgroupCentralizerControl
public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Stellmacher.MainDefs

/-!
# Local centralizer control for conjugates of the central four

Assume the central omega subgroup of a Sylow two-subgroup has order four
and the Sylow subgroup has no normal elementary subgroup of order at least
eight. Every normal elementary four is then central. For a nonidentity
element w of this four, the Sylow subgroup lies in C_G(w), which is solvable
by the N₂ hypothesis. The solvable central-four theorem makes the four
central modulo the odd core of C_G(w), and injectivity of this quotient on
two-subgroups gives the required centralizer control. Group-isomorphism
transport gives the same conclusion for every conjugate of the four.

This is the local consequence of C(w) = C(W) O₂′(C(w)) used in
Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.394, saved in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The odd core is retained throughout the proof.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightCentralFourLocalControl

/-- The centralizer of a nonidentity element of a central Sylow four
controls every two-subgroup containing that four. -/
public theorem centralizes_of_central_four
    {G : Type*} [Group G] [Finite G] (hN2 : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWc : W ≤ center S)
    (w : G) (hw : w ∈ W.map (S : Subgroup G).subtype) (hw1 : w ≠ 1)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hWQ : W.map (S : Subgroup G).subtype ≤ Q)
    (hQC : Q ≤ centralizer ({w} : Set G)) :
    Q ≤ centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  obtain ⟨v, hv, rfl⟩ := hw
  let C := centralizer ({(v : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp (hWc hv) (⟨s, hs⟩ : S))
  let T := S.subtype hSC
  let i : S →* C := inclusion hSC
  have hi : Function.Injective i := inclusion_injective hSC
  have hrange : i.range = (T : Subgroup C) := by
    ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact s.property
    · intro hc
      exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hv1 : v ≠ 1 := by intro h; exact hw1 (congrArg Subtype.val h)
  have hv2 : orderOf (v : G) = 2 := orderOf_eq_prime
    (by simpa using congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian v hv)) hw1
  have hsol : Group.IsSolvable C :=
    hN2 C (Theory.GroupTheory.isTwoLocal_involution_centralizer hv2)
  have hvc : i v ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  have hWiQ : W.map i ≤ Q.subgroupOf C := by
    rintro _ ⟨s, hs, rfl⟩
    exact hWQ (mem_map_of_mem (S : Subgroup G).subtype hs)
  have hlocal := SolvableCentralFour.centralizes_four_of_no_normal_eight
    T i hi hrange hsol hno W hW hWc v hv hv1 hvc
    (Q.subgroupOf C) (hQ.comap_of_injective C.subtype C.subtype_injective) hWiQ
  intro q hq a ha
  obtain ⟨s, hs, rfl⟩ := ha
  exact congrArg Subtype.val
    (hlocal (show (⟨q, hQC hq⟩ : C) ∈ Q.subgroupOf C from hq)
      (i s) (mem_map_of_mem i hs))


/-- A normal elementary four in the central-omega-four case satisfies
the required local centralizer control. -/
public theorem centralizes_four
    {G : Type*} [Group G] [Finite G] (hN2 : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (w : G) (hw : w ∈ W.map (S : Subgroup G).subtype) (hw1 : w ≠ 1)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hWQ : W.map (S : Subgroup G).subtype ≤ Q)
    (hQC : Q ≤ centralizer ({w} : Set G)) :
    Q ≤ centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  have hWc : W ≤ center S :=
    (normal_elementary_le_omega_center_of_no_normal_eight hno hZ W).trans
      (map_subtype_le _)
  exact centralizes_of_central_four hN2 S hno W hW hWc w hw hw1 Q hQ hWQ hQC

/-- Every two-subgroup containing a conjugate of the central four and
centralizing one of its nonidentity elements centralizes the entire conjugate. -/
public theorem centralizes_conjugate_four
    {G : Type*} [Group G] [Finite G] (hN2 : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (g : G) :
    let A := W.map (S : Subgroup G).subtype
    let B := A.map (MulAut.conj g).toMonoidHom
    ∀ w : G, w ∈ B → w ≠ 1 →
      ∀ Q : Subgroup G, IsPGroup 2 Q → B ≤ Q →
        Q ≤ centralizer ({w} : Set G) → Q ≤ centralizer (B : Set G) := by
  intro A B w hw hw1 Q hQ hBQ hQC
  exact centralizes_map_of_two_subgroup_control A
    (centralizes_four hN2 S hZ hno W hW) (MulAut.conj g) w hw hw1 Q hQ hBQ hQC

end Stellmacher.Recognition.NormalEightCentralFourLocalControl
