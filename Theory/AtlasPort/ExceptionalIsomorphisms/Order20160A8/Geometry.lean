module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Reconstructing the eight points from the binary quadratic space

The 28 nonsingular vectors are the duads of eight points. Two distinct duads
have nonsingular sum precisely when they meet. Three meeting duads which do
not form a triangle have a common vertex; every duad meeting all three also
contains that vertex. An isometry therefore permutes the eight stars. The
seven duads through a vertex span the space, so this permutation determines
the isometry and bounds the full isometry group by 8!.

The displayed vectors come from the hyperbolic basis in ATLAS
`Comparisons/Exceptional/DeletedEightSplit.lean`. This incidence proof replaces
the general orthogonal order and Dickson-invariant imports of
`Comparisons/Exceptional/Order20160A8.lean`. Only the small coordinate identities
are checked by kernel reduction; the reconstruction is proved structurally.
-/

noncomputable section
namespace Atlas.Order20160A8.Geometry
open ClassicalOrthogonal
abbrev D := VectorD 3 (ZMod 2)
abbrev Q := formD 3 (ZMod 2)

def point : Fin 8 → D := ![
  Sum.elim ![0,0,0] ![0,0,0],
  Sum.elim ![0,1,0] ![0,1,0],
  Sum.elim ![0,0,1] ![0,1,1],
  Sum.elim ![1,1,1] ![0,0,1],
  Sum.elim ![0,1,1] ![1,0,1],
  Sum.elim ![1,1,0] ![1,0,0],
  Sum.elim ![1,0,0] ![1,1,1],
  Sum.elim ![1,0,1] ![1,1,0]]

theorem add_self (x : D) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

def edge (i j : Fin 8) : D := point i + point j

theorem point_injective : Function.Injective point := by decide +kernel
@[simp] theorem point_zero : point 0 = 0 := by decide +kernel
@[simp] theorem edge_same (i : Fin 8) : edge i i = 0 := add_self _
theorem edge_comm (i j : Fin 8) : edge i j = edge j i := add_comm _ _
theorem edge_injective (i : Fin 8) : Function.Injective (edge i) := by
  intro j k h
  exact point_injective (add_left_cancel h)

theorem edge_add (a b c : Fin 8) : edge a b + edge a c = edge b c := by
  simp only [edge]
  rw [add_add_add_comm, add_self, zero_add]

theorem edge_value : ∀ i j : Fin 8, Q (edge i j) = if i = j then 0 else 1 := by
  decide +kernel

theorem nonsingular_exists : ∀ x : D, Q x = 1 → ∃ i j : Fin 8, i ≠ j ∧ x = edge i j := by
  decide +kernel

theorem edge_intersect : ∀ a b c d : Fin 8, a ≠ b → c ≠ d → Q (edge a b + edge c d) = 1 →
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  decide +kernel

theorem adjacent_exists (u v : D) (hu : Q u = 1) (hv : Q v = 1) (huv : Q (u + v) = 1) :
    ∃ a b c : Fin 8, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ u = edge a b ∧ v = edge a c := by
  obtain ⟨a,b,hab,rfl⟩ := nonsingular_exists u hu
  obtain ⟨c,d,hcd,rfl⟩ := nonsingular_exists v hv
  have hne : edge a b ≠ edge c d := by
    intro he
    rw [he, add_self, map_zero] at huv
    exact zero_ne_one huv
  rcases edge_intersect a b c d hab hcd huv with h | h | h | h
  · subst c
    exact ⟨a,b,d,hab,hcd, fun h => hne (by rw [h]),rfl,rfl⟩
  · subst d
    refine ⟨a,b,c,hab,Ne.symm hcd,?_,rfl,edge_comm c a⟩
    intro h
    exact hne (by rw [h, edge_comm])
  · subst c
    refine ⟨b,a,d,Ne.symm hab,hcd,?_,edge_comm a b,rfl⟩
    intro h
    exact hne (by rw [h, edge_comm])
  · subst d
    refine ⟨b,a,c,Ne.symm hab,Ne.symm hcd,?_,edge_comm a b,edge_comm c b⟩
    intro h
    exact hne (by rw [h])

theorem third_through (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (w : D)
    (hw : Q w = 1) (hb : Q (w + edge a b) = 1) (hc : Q (w + edge a c) = 1)
    (hne : w ≠ edge b c) : ∃ d, w = edge a d := by
  obtain ⟨u,v,huv,rfl⟩ := nonsingular_exists w hw
  have h1 := edge_intersect u v a b huv hab hb
  have h2 := edge_intersect u v a c huv hac hc
  by_cases h : u = a
  · exact ⟨v, by rw [h]⟩
  by_cases h' : v = a
  · exact ⟨u, by rw [h', edge_comm]⟩
  have hb' : u = b ∨ v = b := by tauto
  have hc' : u = c ∨ v = c := by tauto
  rcases hb' with rfl | rfl <;> rcases hc' with hbc' | hbc'
  · exact (hbc hbc').elim
  · exact (hne (by rw [hbc'])).elim
  · exact (hne (by rw [hbc', edge_comm])).elim
  · exact (hbc hbc').elim

theorem through_three (a b c d : Fin 8) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (w : D) (hw : Q w = 1) (hb : Q (w + edge a b) = 1)
    (hc : Q (w + edge a c) = 1) (hd : Q (w + edge a d) = 1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) : ∃ e, w = edge a e := by
  apply third_through a b c hab hac hbc w hw hb hc
  intro he
  rw [he] at hd
  have h := edge_intersect b c a d hbc had hd
  tauto

/-- The seven nonzero displayed points span the six-dimensional space. -/
theorem ext_points {f g : D →ₗ[ZMod 2] D} (h : ∀ i, f (point i) = g (point i)) : f = g := by
  apply (Pi.basisFun (ZMod 2) (Index 3)).ext
  intro i
  have test : ∀ i : Index 3, ∃ s : Finset (Fin 8), Pi.single i (1 : ZMod 2) = ∑ j ∈ s, point j := by
    intro i
    rcases i with i | i <;> fin_cases i
    · exact ⟨{1,2,3}, by decide +kernel⟩
    · exact ⟨{3,4,5}, by decide +kernel⟩
    · exact ⟨{2,3,4,6}, by decide +kernel⟩
    · exact ⟨{1,2,4}, by decide +kernel⟩
    · exact ⟨{1,3,4,5}, by decide +kernel⟩
    · exact ⟨{1,5,6}, by decide +kernel⟩
  obtain ⟨s,hs⟩ := test i
  simp only [Pi.basisFun_apply, hs, map_sum, h]


/-- The duad incidence reconstructs the eight vertices from any quadratic isometry. -/
theorem exists_permutation (g : O_DPlus 3 (ZMod 2)) :
    ∃ p : Equiv.Perm (Fin 8), ∀ i, g.val (point i) = edge (p 0) (p i) := by
  have hg := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup Q g.val).mp g.property
  have hv (i : Fin 8) (hi : i ≠ 0) : Q (g.val (point i)) = 1 := by
    rw [hg]
    simpa [edge, hi, Ne.symm hi] using edge_value 0 i
  have ha (i j : Fin 8) (hij : i ≠ j) :
      Q (g.val (point i) + g.val (point j)) = 1 := by
    rw [← map_add, hg]
    simpa only [edge, if_neg hij] using edge_value i j
  obtain ⟨a,b,c,hab,hac,hbc,hb,hc⟩ := adjacent_exists
    (g.val (point 1)) (g.val (point 2)) (hv 1 (by decide)) (hv 2 (by decide))
    (ha 1 2 (by decide))
  have hne : g.val (point 3) ≠ edge b c := by
    rw [← edge_add a b c, ← hb, ← hc, ← map_add]
    intro he
    have hh := g.val.injective he
    exact (by decide +kernel : point 3 ≠ point 1 + point 2) hh
  obtain ⟨d,hd⟩ := third_through a b c hab hac hbc (g.val (point 3)) (hv 3 (by decide))
    (by rw [← hb]; exact ha 3 1 (by decide))
    (by rw [← hc]; exact ha 3 2 (by decide)) hne
  have had : a ≠ d := by
    intro he
    have hh := hv 3 (by decide)
    rw [hd, ← he, edge_same, map_zero] at hh
    exact zero_ne_one hh
  have hbd : b ≠ d := by
    intro he
    have hh := g.val.injective (hb.trans ((congrArg (edge a) he).trans hd.symm))
    exact (by decide : (1 : Fin 8) ≠ 3) (point_injective hh)
  have hcd : c ≠ d := by
    intro he
    have hh := g.val.injective (hc.trans ((congrArg (edge a) he).trans hd.symm))
    exact (by decide : (2 : Fin 8) ≠ 3) (point_injective hh)
  have hex (i : Fin 8) : ∃ j, g.val (point i) = edge a j := by
    by_cases h0 : i = 0
    · subst i; exact ⟨a, by simp⟩
    by_cases h1 : i = 1
    · subst i; exact ⟨b,hb⟩
    by_cases h2 : i = 2
    · subst i; exact ⟨c,hc⟩
    by_cases h3 : i = 3
    · subst i; exact ⟨d,hd⟩
    exact through_three a b c d hbc hbd hcd (g.val (point i)) (hv i h0)
      (by rw [← hb]; exact ha i 1 h1)
      (by rw [← hc]; exact ha i 2 h2)
      (by rw [← hd]; exact ha i 3 h3) hab hac had
  choose r hr using hex
  have hinj : Function.Injective r := by
    intro i j he
    apply point_injective
    apply g.val.injective
    rw [hr, hr, he]
  let p : Equiv.Perm (Fin 8) := Equiv.ofBijective r
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have h0 : r 0 = a := by
    apply edge_injective a
    rw [← hr, point_zero, map_zero, edge_same]
  refine ⟨p, fun i => ?_⟩
  change g.val (point i) = edge (r 0) (r i)
  rw [h0, hr]

/-- A quadratic isometry is determined by its reconstructed permutation. -/
public theorem orthogonal_card_le : Nat.card (O_DPlus 3 (ZMod 2)) ≤ 40320 := by
  let encode (g : O_DPlus 3 (ZMod 2)) := (exists_permutation g).choose
  have hencode (g : O_DPlus 3 (ZMod 2)) := (exists_permutation g).choose_spec
  have hinj : Function.Injective encode := by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply ext_points
    intro i
    change g.val (point i) = h.val (point i)
    rw [hencode g, hencode h]
    change edge (encode g 0) (encode g i) = edge (encode h 0) (encode h i)
    rw [he]
  have h := Nat.card_le_card_of_injective encode hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using h

end Atlas.Order20160A8.Geometry
