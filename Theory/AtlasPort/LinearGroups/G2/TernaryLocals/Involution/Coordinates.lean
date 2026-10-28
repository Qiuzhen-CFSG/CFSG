module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals
import Mathlib.Tactic.LinearCombination

/-!
# Coordinates for the ternary G₂ involution centralizer

The involution `torus (-1) 1` fixes a four-dimensional split quaternion algebra
and negates its four-dimensional complement. Write `u = e₁`, `v = -e₆`, and
`w = e₀ + e₇`. The two matrix units `u,v` and the odd norm-one vector `w`
generate the octonion algebra: `columns_basis` reconstructs all eight basis
vectors from them. Thus their three images determine any automorphism.

A centralizing automorphism sends `u,v` to trace-zero fixed vectors with zero
norm and polarized norm -1, and sends `w` to an odd norm-one vector. Over F₃
there are 24 choices for the matrix-unit pair and 24 for the odd vector. The
resulting injection bounds the actual centralizer order by 576. Realizing
all frames, or proving a matching lower bound, is a separate assertion.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Main Theorem 0.1.2(4), printed pp.3–4 (repeated on pp.481–482), and
configuration I.4(G1), printed p.417. No local configuration is assumed here.
Coordinates use the licensed ATLAS split-octonion port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.Involution
open Atlas.SplitOctonion

abbrev K := ZMod 3
abbrev Triple := Fin 3 → K
abbrev Quad := Fin 4 → K
abbrev P := localSubgroup false

def qnorm (a : Triple) : K := a 0 * a 2 - a 1 ^ 2
def pairing (a b : Triple) : K := a 0 * b 2 + a 2 * b 0 + a 1 * b 1
abbrev MatrixUnits := {p : Triple × Triple //
  qnorm p.1 = 0 ∧ qnorm p.2 = 0 ∧ pairing p.1 p.2 = -1}
abbrev NormOne := {a : Quad // a 0 * a 3 + a 1 * a 2 = 1}
abbrev Frame := MatrixUnits × NormOne

set_option maxRecDepth 100000

/-- The 24 possible images of the two fixed matrix units. -/
theorem card_matrixUnits : Nat.card MatrixUnits = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The 24 norm-one vectors in the negative eigenspace. -/
theorem card_normOne : Nat.card NormOne = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Exactly 576 admissible image frames, before asserting realization. -/
theorem card_frame : Nat.card Frame = 576 := by
  rw [Nat.card_prod, card_matrixUnits, card_normOne]

def fixedEmbed (a : Triple) : Carrier K := ![0,a 0,0,a 1,-a 1,0,a 2,0]
def oddEmbed (a : Quad) : Carrier K := ![a 0,0,a 1,0,0,a 2,0,a 3]
def fixedCoordinates (x : Carrier K) : Triple := ![x 1,x 3,x 6]
def oddCoordinates (x : Carrier K) : Quad := ![x 0,x 2,x 5,x 7]

def u : Carrier K := basisVector 1
def v : Carrier K := -basisVector 6
def w : Carrier K := basisVector 0 + basisVector 7

private theorem neg_eq_self_iff (z : K) : -z = z ↔ z = 0 := by
  exact (by decide +kernel : ∀ z : K, -z = z ↔ z = 0) z

private theorem self_eq_neg_iff (z : K) : z = -z ↔ z = 0 := by
  exact (by decide +kernel : ∀ z : K, z = -z ↔ z = 0) z

theorem involution_apply (x : Carrier K) :
    involution.val x = ![-x 0,x 1,-x 2,x 3,x 4,-x 5,x 6,-x 7] := by
  have hw : ∀ i : Fin 8, (torusWeights (-1 : Kˣ) 1 i : K) =
      (![-1,1,-1,1,1,-1,1,-1] : Carrier K) i := by decide +kernel
  change (fun i => (torusWeights (-1 : Kˣ) 1 i : K) * x i) = _
  simp_rw [hw]
  ext i
  fin_cases i <;> simp

theorem fixed_iff (x : Carrier K) : involution.val x = x ↔
    x 0 = 0 ∧ x 2 = 0 ∧ x 5 = 0 ∧ x 7 = 0 := by
  rw [involution_apply, funext_iff]
  simp [Fin.forall_fin_succ, neg_eq_self_iff]

theorem odd_iff (x : Carrier K) : involution.val x = -x ↔
    x 1 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 6 = 0 := by
  rw [involution_apply, funext_iff]
  simp [Fin.forall_fin_succ, self_eq_neg_iff]

theorem fixed_reconstruct (x : Carrier K) (hx : involution.val x = x)
    (ht : trace x = 0) : fixedEmbed (fixedCoordinates x) = x := by
  obtain ⟨h0,h2,h5,h7⟩ := (fixed_iff x).mp hx
  have h4 : -x 3 = x 4 := (eq_neg_of_add_eq_zero_right ht).symm
  ext i
  fin_cases i <;> simp [fixedEmbed, fixedCoordinates, h0, h2, h5, h7, h4]

theorem odd_reconstruct (x : Carrier K) (hx : involution.val x = -x) :
    oddEmbed (oddCoordinates x) = x := by
  obtain ⟨h1,h3,h4,h6⟩ := (odd_iff x).mp hx
  ext i
  fin_cases i <;> simp [oddEmbed, oddCoordinates, h1, h3, h4, h6]

theorem commute_apply (g : P) (x : Carrier K) :
    g.val.val (involution.val x) = involution.val (g.val.val x) := by
  have hg : g.val ∈ Subgroup.centralizer {involution} := by
    rw [← localSubgroup_false]
    exact g.property
  have h := Subgroup.mem_centralizer_singleton_iff.mp hg
  exact congrArg (fun a : Model K => a.val x) h

theorem map_fixed (g : P) (x : Carrier K) (hx : involution.val x = x) :
    involution.val (g.val.val x) = g.val.val x := by
  rw [← commute_apply, hx]

theorem map_odd (g : P) (x : Carrier K) (hx : involution.val x = -x) :
    involution.val (g.val.val x) = -g.val.val x := by
  rw [← commute_apply, hx, map_neg]

theorem map_u (g : P) :
    fixedEmbed (fixedCoordinates (g.val.val u)) = g.val.val u := by
  apply fixed_reconstruct
  · exact map_fixed g u (by decide +kernel)
  · rw [automorphism_trace]
    decide +kernel

theorem map_v (g : P) :
    fixedEmbed (fixedCoordinates (g.val.val v)) = g.val.val v := by
  apply fixed_reconstruct
  · exact map_fixed g v (by decide +kernel)
  · rw [automorphism_trace]
    decide +kernel

theorem map_w (g : P) :
    oddEmbed (oddCoordinates (g.val.val w)) = g.val.val w :=
  odd_reconstruct _ (map_odd g w (by decide +kernel))

theorem norm_fixedEmbed (a : Triple) : norm (fixedEmbed a) = qnorm a := by
  simp [SplitOctonion.norm, fixedEmbed, qnorm, pow_two, sub_eq_add_neg]

theorem norm_fixed_add (a b : Triple) :
    norm (fixedEmbed a + fixedEmbed b) = qnorm a + qnorm b + pairing a b := by
  have hthree : (3 : K) = 0 := by decide
  simp [SplitOctonion.norm, fixedEmbed, qnorm, pairing]
  linear_combination -(a 1 * b 1) * hthree

/-- The image frame of an actual element of the involution centralizer. -/
def encode (g : P) : Frame :=
  (⟨(fixedCoordinates (g.val.val u), fixedCoordinates (g.val.val v)), by
    have hu : qnorm (fixedCoordinates (g.val.val u)) = 0 := by
      rw [← norm_fixedEmbed, map_u, automorphism_norm]
      decide +kernel
    have hv : qnorm (fixedCoordinates (g.val.val v)) = 0 := by
      rw [← norm_fixedEmbed, map_v, automorphism_norm]
      decide +kernel
    refine ⟨hu, hv, ?_⟩
    have h := automorphism_norm g.val (u + v)
    rw [map_add, ← map_u, ← map_v, norm_fixed_add, hu, hv, zero_add, zero_add] at h
    exact h⟩,
   ⟨oddCoordinates (g.val.val w), by
     have h := automorphism_norm g.val w
     rw [← map_w] at h
     simpa [SplitOctonion.norm, oddEmbed, w, basisVector] using h⟩)

/-- All eight basis images reconstructed from the two matrix units and one odd unit. -/
def columns (a b c : Carrier K) : Fin 8 → Carrier K :=
  ![mul (mul b a) c, a, -mul b c, mul b a, mul a b, mul a c, -b, mul (mul a b) c]

theorem columns_basis (i : Fin 8) : columns u v w i = basisVector i := by
  exact (by decide +kernel : ∀ i : Fin 8, columns u v w i = basisVector i) i

theorem map_columns (g : Model K) (a b c : Carrier K) (i : Fin 8) :
    g.val (columns a b c i) = columns (g.val a) (g.val b) (g.val c) i := by
  fin_cases i <;> simp [columns]

/-- The three displayed octonions determine any multiplication-preserving automorphism. -/
theorem ext_generators (g h : Model K)
    (hu : g.val u = h.val u) (hv : g.val v = h.val v) (hw : g.val w = h.val w) :
    g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext
  intro i
  change g.val (basisVector i) = h.val (basisVector i)
  rw [← columns_basis, map_columns, map_columns, hu, hv, hw]

theorem encode_injective : Function.Injective encode := by
  intro g h he
  have hu := congrArg (fun f : Frame => f.1.val.1) he
  have hv := congrArg (fun f : Frame => f.1.val.2) he
  have hw := congrArg (fun f : Frame => f.2.val) he
  apply Subtype.ext
  apply ext_generators
  · exact (map_u g).symm.trans ((congrArg fixedEmbed hu).trans (map_u h))
  · exact (map_v g).symm.trans ((congrArg fixedEmbed hv).trans (map_v h))
  · exact (map_w g).symm.trans ((congrArg oddEmbed hw).trans (map_w h))

/-- An upper bound on the actual involution centralizer, without group-order input. -/
theorem card_le : Nat.card P ≤ 576 := by
  simpa only [card_frame] using Nat.card_le_card_of_injective encode encode_injective

end Atlas.G2.TernaryLocals.Involution
