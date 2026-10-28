module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Five

/-!
# Assembly of the corrected H.9 adapted-pair transport

A standard coordinate pair, with its actual Sylow intersection and fixed-line
calculation proved, suffices for every Sylow subgroup and every prescribed
two-subgroup fixing a nonsingular vector. Both the actor and the point are
conjugated by the same inner automorphism. The geometric moving space is
ker(f) ⊕ ann(x); identifying it with the commutator space remains with the
nonsingular-stabilizer calculation.

`adapted_pair_of_standard_coordinates` is the general assembly lemma.
`adapted_pair_four` and `adapted_pair_five` discharge all of its standard
Sylow, fixed-space, movement and transitivity premises using the explicit
coordinate calculations. They retain only the specified coordinate action,
inner index two and nonsingular stabilizer order as ordinary model inputs.
The source assembly must construct these inputs, compare the coordinate
action with the source module, and identify the inner point stabilizer with
the source two-residual. No source-numbered theorem is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(4),
printed p.390, as corrected by the source audit of 6 October 2026;
consumers 12.1.1 and 12.1.3, printed pp.788–790.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual BinaryNaturalDual.AdaptedPair

/-- Conditional assembly from the explicit standard coordinate calculation.
Every additional standard input is listed here; none is supplied by a
record projection or an assumed conclusion for the arbitrary input pair. -/
theorem adapted_pair_of_standard_coordinates {n : ℕ} (d : CoordinateAction n)
    (hindex : (innerGroup n).index = 2)
    (S : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (w : CoordinateSpace n) (hw : quadratic w = 1)
    (htrans : ∀ v : CoordinateSpace n, quadratic v = 1 →
      ∃ l ∈ innerGroup n, linearAction d l v = w)
    (P : Sylow 2 (pointStabilizer (linearAction d) w))
    (hP : (P : Subgroup (pointStabilizer (linearAction d) w)).map
      (pointStabilizer (linearAction d) w).subtype =
        (S : Subgroup _) ⊓ pointStabilizer (linearAction d) w)
    (houter : ∃ s : pointStabilizer (linearAction d) w,
      s ∈ (P : Subgroup _) ∧ (s : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) ∉ innerGroup n)
    (hfixed : movingSpace w ⊓ fixedVectors (linearAction d)
      ((S : Subgroup _) ⊓ pointStabilizer (linearAction d) w) = fixedVectors (linearAction d) S)
    (hdim : Module.finrank (ZMod 2) (fixedVectors (linearAction d) S) = 1)
    (hmoves : ∃ a ∈ innerGroup n, linearAction d a w = w ∧
      ∃ z ∈ fixedVectors (linearAction d) S, linearAction d a z ≠ z)
    (T : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (v : CoordinateSpace n) (hv : quadratic v = 1)
    (A : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (hA : IsPGroup 2 A) (hAv : A ≤ pointStabilizer (linearAction d) v) :
    ∃ l ∈ innerGroup n, ∃ v' : CoordinateSpace n,
      v' = linearAction d l v ∧ quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (pointStabilizer (linearAction d) v'),
        (Q : Subgroup (pointStabilizer (linearAction d) v')).map
          (pointStabilizer (linearAction d) v').subtype =
          (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') ∧
      A.map (MulAut.conj l).toMonoidHom ≤
        (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v' ∧
      movingSpace v' ⊓ fixedVectors (linearAction d)
        ((T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') =
          fixedVectors (linearAction d) T ∧
      Module.finrank (ZMod 2) (fixedVectors (linearAction d) T) = 1 ∧
      ∃ a ∈ innerGroup n, linearAction d a v' = v' ∧
        ∃ z ∈ fixedVectors (linearAction d) T, linearAction d a z ≠ z := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
      (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
      DFunLike.coe_injective
  let : MulAction (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (CoordinateSpace n) :=
    MulAction.compHom _ (linearAction d)
  obtain ⟨g, hgL, l, hlL, hg, hl, hAl, Q, hQ⟩ :=
    exists_pair_in_arbitrary_sylow (innerGroup n) hindex S T v w (htrans v hv)
      P hP houter A hA hAv
  have hgMap : (S : Subgroup _).map (MulAut.conj g).toMonoidHom = (T : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨l, hlL, linearAction d g w, hl.symm, ?_, ⟨Q, hQ⟩, hAl, ?_, ?_, ?_⟩
  · rw [quadratic_innerActor d g hgL, hw]
  · have he := movingSpace_fixedVectors_map_inner d g hgL (S : Subgroup _) w
    rw [hfixed, fixedVectors_map_conj, hgMap] at he
    exact he.symm
  · rw [← hgMap, finrank_fixedVectors_conj]
    exact hdim
  · have hm := moves_fixedVectors_conj (linearAction d) (innerGroup n)
      (S : Subgroup _) g hgL w hmoves
    rw [hgMap] at hm
    exact hm

/-- The corrected adapted-pair conclusion in dimension four, for any actual
ambient Sylow and any two-subgroup fixing the input nonsingular vector.
The same inner element transports the vector and its actor. All standard
coordinate witnesses and their fixed-line properties are proved; only the
ordinary action, index and stabilizer-order inputs remain for source assembly. -/
theorem adapted_pair_four (d : CoordinateAction 4)
    (hindex : (innerGroup 4).index = 2)
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFour) = 336)
    (T : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup 4)))
    (v : CoordinateSpace 4) (hv : quadratic v = 1)
    (A : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup 4)))
    (hA : IsPGroup 2 A) (hAv : A ≤ pointStabilizer (linearAction d) v) :
    ∃ l ∈ innerGroup 4, ∃ v' : CoordinateSpace 4,
      v' = linearAction d l v ∧ quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (pointStabilizer (linearAction d) v'),
        (Q : Subgroup (pointStabilizer (linearAction d) v')).map
          (pointStabilizer (linearAction d) v').subtype =
          (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') ∧
      A.map (MulAut.conj l).toMonoidHom ≤
        (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v' ∧
      movingSpace v' ⊓ fixedVectors (linearAction d)
        ((T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') =
          fixedVectors (linearAction d) T ∧
      Module.finrank (ZMod 2) (fixedVectors (linearAction d) T) = 1 ∧
      ∃ a ∈ innerGroup 4, linearAction d a v' = v' ∧
        ∃ z ∈ fixedVectors (linearAction d) T, linearAction d a z ≠ z := by
  obtain ⟨S, P, _hS, hw, htrans, hP, houter, hfixed, hdim, hmoves⟩ :=
    Four.standard_coordinates d hindex hcard
  exact adapted_pair_of_standard_coordinates d hindex S vectorFour hw htrans
    P hP houter hfixed hdim hmoves T v hv A hA hAv

/-- The corrected adapted-pair conclusion in dimension five. In particular,
the prescribed actor is carried into the centralizer in the original Sylow,
whose fixed vectors in ker(f) ⊕ ann(x) equal that Sylow's one-dimensional
fixed space. The inner point stabilizer does not centralize this line. -/
theorem adapted_pair_five (d : CoordinateAction 5)
    (hindex : (innerGroup 5).index = 2)
    (hcard : Nat.card (pointStabilizer (linearAction d) vectorFive) = 40320)
    (T : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup 5)))
    (v : CoordinateSpace 5) (hv : quadratic v = 1)
    (A : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup 5)))
    (hA : IsPGroup 2 A) (hAv : A ≤ pointStabilizer (linearAction d) v) :
    ∃ l ∈ innerGroup 5, ∃ v' : CoordinateSpace 5,
      v' = linearAction d l v ∧ quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (pointStabilizer (linearAction d) v'),
        (Q : Subgroup (pointStabilizer (linearAction d) v')).map
          (pointStabilizer (linearAction d) v').subtype =
          (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') ∧
      A.map (MulAut.conj l).toMonoidHom ≤
        (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v' ∧
      movingSpace v' ⊓ fixedVectors (linearAction d)
        ((T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') =
          fixedVectors (linearAction d) T ∧
      Module.finrank (ZMod 2) (fixedVectors (linearAction d) T) = 1 ∧
      ∃ a ∈ innerGroup 5, linearAction d a v' = v' ∧
        ∃ z ∈ fixedVectors (linearAction d) T, linearAction d a z ≠ z := by
  obtain ⟨S, P, _hS, hw, htrans, hP, houter, hfixed, hdim, hmoves⟩ :=
    Five.standard_coordinates d hindex hcard
  exact adapted_pair_of_standard_coordinates d hindex S vectorFive hw htrans
    P hP houter hfixed hdim hmoves T v hv A hA hAv

end CFSG.Quasithin.ChapterH.NaturalDual
