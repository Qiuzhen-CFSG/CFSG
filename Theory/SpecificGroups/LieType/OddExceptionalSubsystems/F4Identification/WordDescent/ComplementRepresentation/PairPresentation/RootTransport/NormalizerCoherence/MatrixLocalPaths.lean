module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Assembling matrix normalizer paths from Weyl geometry and Tits identities

The source argument has three distinct ingredients: a two-node factorization
of a marked Weyl element, transport of signed simple-root curves by the
literal Tits matrices, and a product of simple Tits squares comparing two
words with equal Weyl product. This module states those independent contracts
and proves their assembly into the actual matrix paths. It does not assert
any of the three inputs or unconditional path existence.

Finiteness of the matrix cover replaces inverses by positive words. Weyl
paths lift one pair segment at a time, retaining the parameters supplied by
actual matrix equalities. The square correction acts afterwards, so the
resulting path represents the original matrix, rather than only its Weyl
image. An empty local segment identifies the final marked parameter using
the original conjugation equality.

Source: GLS3 Lemma 2.9.4 and the root-transport argument following Theorem
2.9.3, `refs/KGroup/GLS3/chapter2.tex`, lines 1399--1454.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

abbrev Node := typeF4RootPairing_base.support

variable (F : Type*) [Field F]

/-- Evaluation of a positive word of the parameter-one Tits matrices. -/
def titsEvaluation (w : List Node) : Cover F :=
  coverEvaluation F (transportTitsWord F w)

@[simp] theorem titsEvaluation_nil : titsEvaluation F [] = 1 := by
  simp [titsEvaluation]

theorem titsEvaluation_append (v w : List Node) :
    titsEvaluation F (v ++ w) = titsEvaluation F v * titsEvaluation F w := by
  simp only [titsEvaluation, transportTitsWord_append, map_mul]

theorem pair_titsEvaluation (i j : Fin 4) (v : List Bool) :
    pairEvaluation F i j (pairTransportTitsWord F v) =
      titsEvaluation F (pairTransportNodes i j v) := by
  change coverEvaluation F (pairInclusion F i j (pairTransportTitsWord F v)) = _
  rw [pairInclusion_pairTransportTitsWord]
  rfl

/-- Every element of the finite matrix normalizer has a positive Tits word.
This justifies replacing inverse generators without using any presentation. -/
theorem exists_positive_word [Finite F] {n : Cover F}
    (hn : n ∈ coverTransportNormalizer F) :
    ∃ w : List Node, titsEvaluation F w = n := by
  have hm : n ∈ Submonoid.closure (Set.range fun i : Node => titsEvaluation F [i]) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hn
  clear hn
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], rfl⟩
  | one => exact ⟨[], titsEvaluation_nil F⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨v, rfl⟩ := ihx
    obtain ⟨w, rfl⟩ := ihy
    exact ⟨v ++ w, titsEvaluation_append F v w⟩

/-- A matrix path proves its literal conjugation equation. -/
theorem path_conjugates {n : Cover F} {x y : Bool × Fin 4 × F}
    (h : NormalizerTransportPath F n x y) :
    n * coverSimple F x.1 x.2.1 x.2.2 * n⁻¹ =
      coverSimple F y.1 y.2.1 y.2.2 := by
  induction h with
  | refl x => simp
  | localStep i j v s k z l t u h => exact h
  | @trans n m x y z hn hm ihn ihm =>
    calc
      _ = m * (n * coverSimple F x.1 x.2.1 x.2.2 * n⁻¹) * m⁻¹ := by group
      _ = _ := by rw [ihn, ihm]

/-- Equality of two marked matrix elements is an empty local segment. -/
theorem path_of_element_eq (s z : Bool) (i j : Fin 4) (t u : F)
    (h : coverSimple F s i t = coverSimple F z j u) :
    NormalizerTransportPath F 1 (s, i, t) (z, j, u) := by
  have hc : pairEvaluation F i j (pairTransportTitsWord F []) *
      coverSimple F s (pairNode i j true) t *
      (pairEvaluation F i j (pairTransportTitsWord F []))⁻¹ =
      coverSimple F z (pairNode i j false) u := by
    simpa only [pairTransportTitsWord, map_one, pairNode, Bool.false_eq_true, ite_true, ite_false,
      one_mul, inv_one, mul_one] using h
  simpa only [pairTransportTitsWord, map_one, pairNode, Bool.false_eq_true, ite_true, ite_false] using
    NormalizerTransportPath.localStep (F := F) i j [] s true z false t u hc

/-- A word in simple Tits squares, still written as a positive Tits word. -/
def squareWord (d : List Node) : List Node := d.flatMap fun i => [i, i]

@[simp] theorem squareWord_nil : squareWord [] = [] := rfl

@[simp] theorem squareWord_cons (i : Node) (d : List Node) :
    squareWord (i :: d) = [i, i] ++ squareWord d := rfl

/-- A two-node factorization in the actual F4 Weyl group. The endpoints of
segments are signed numbered simple roots. Composition has the matrix order. -/
inductive WeylPairPath :
    typeF4RootPairing.weylGroup → (Bool × Fin 4) → (Bool × Fin 4) → Prop
  | refl (x) : WeylPairPath 1 x x
  | localStep (i j : Fin 4) (v : List Bool) (s k z l : Bool)
      (h : typeF4RootPairing.weylGroupToPerm
          (typeF4RootPairing_base.wordProd (pairTransportNodes i j v))
          (signedRoot s (pairNode i j k)) = signedRoot z (pairNode i j l)) :
      WeylPairPath (typeF4RootPairing_base.wordProd (pairTransportNodes i j v))
        (s, pairNode i j k) (z, pairNode i j l)
  | trans {n m x y z} (hn : WeylPairPath n x y) (hm : WeylPairPath m y z) :
      WeylPairPath (m * n) x z

/-- The geometric relation retains the actual Weyl endpoint. -/
theorem WeylPairPath.endpoint
    {g : typeF4RootPairing.weylGroup} {x y : Bool × Fin 4}
    (h : WeylPairPath g x y) :
    typeF4RootPairing.weylGroupToPerm g (signedRoot x.1 x.2) =
      signedRoot y.1 y.2 := by
  induction h with
  | refl x => rfl
  | localStep i j v s k z l h => exact h
  | @trans n m x y z hn hm ihn ihm =>
    change typeF4RootPairing.weylGroupToPerm m
      (typeF4RootPairing.weylGroupToPerm n (signedRoot x.1 x.2)) = _
    rw [ihn, ihm]

/-- The geometric content of GLS3 Lemma 2.9.4 after compressing consecutive
steps in a common simple-root plane. No Tits matrix comparison is included. -/
def HasWeylPairPaths : Prop :=
  ∀ (w : List Node) (s z : Bool) (i j : Fin 4),
    typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd w)
      (signedRoot s i) = signedRoot z j →
    WeylPairPath (typeF4RootPairing_base.wordProd w) (s, i) (z, j)

/-- Transport of signed simple curves, and recognition of the Weyl endpoint
from a nonidentity matrix element. All parameter equalities are literal. -/
structure SimpleTransport : Prop where
  map : ∀ (w : List Node) (s z : Bool) (i j : Fin 4),
    typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd w)
      (signedRoot s i) = signedRoot z j →
    ∀ t : F, ∃ u : F,
      titsEvaluation F w * coverSimple F s i t * (titsEvaluation F w)⁻¹ =
        coverSimple F z j u
  recognize : ∀ (w : List Node) (s z : Bool) (i j : Fin 4) (t u : F),
    coverSimple F s i t ≠ 1 →
    titsEvaluation F w * coverSimple F s i t * (titsEvaluation F w)⁻¹ =
      coverSimple F z j u →
    typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd w)
      (signedRoot s i) = signedRoot z j

/-- The discrepancy of two Tits words with equal Weyl product is a product
of simple Tits squares on the left. This is an actual-matrix statement. -/
def HasSquareCorrections : Prop :=
  ∀ w v : List Node,
    typeF4RootPairing_base.wordProd w = typeF4RootPairing_base.wordProd v →
    ∃ d : List Node,
      titsEvaluation F w = titsEvaluation F (squareWord d) * titsEvaluation F v

/-- Lift a Weyl pair path to a positive matrix word with the same Weyl
product, supplying each intermediate parameter through matrix transport. -/
theorem lift_weyl_path (hc : SimpleTransport F)
    {g : typeF4RootPairing.weylGroup} {x y : Bool × Fin 4}
    (h : WeylPairPath g x y) (t : F) :
    ∃ (w : List Node), typeF4RootPairing_base.wordProd w = g ∧
      ∃ u : F, NormalizerTransportPath F (titsEvaluation F w)
        (x.1, x.2, t) (y.1, y.2, u) := by
  induction h generalizing t with
  | refl x =>
    exact ⟨[], typeF4RootPairing_base.wordProd_nil, t, by
      rw [titsEvaluation_nil]
      exact NormalizerTransportPath.refl (F := F) _⟩
  | localStep i j v s k z l h =>
    obtain ⟨u, hu⟩ := hc.map (pairTransportNodes i j v) s z
      (pairNode i j k) (pairNode i j l) h t
    refine ⟨pairTransportNodes i j v, rfl, u, ?_⟩
    rw [← pair_titsEvaluation] at hu ⊢
    exact NormalizerTransportPath.localStep (F := F) i j v s k z l t u hu
  | @trans n m x y z hn hm ihn ihm =>
    obtain ⟨v, hv, u, hu⟩ := ihn t
    obtain ⟨w, hw, a, ha⟩ := ihm u
    refine ⟨w ++ v, ?_, a, ?_⟩
    · rw [typeF4RootPairing_base.wordProd_append, hw, hv]
    · rw [titsEvaluation_append]
      exact NormalizerTransportPath.trans hu ha

/-- One simple Tits square gives a local path at every signed simple root. -/
theorem path_square (hc : SimpleTransport F) (q : Node)
    (s : Bool) (j : Fin 4) (t : F) :
    ∃ u : F, NormalizerTransportPath F (titsEvaluation F [q, q])
      (s, j, t) (s, j, u) := by
  have hw : typeF4RootPairing_base.wordProd [q, q] = 1 := by
    simp only [RootPairing.Base.wordProd_cons, RootPairing.Base.wordProd_nil,
      mul_one, RootPairing.Base.simpleReflection_mul_self]
  obtain ⟨u, hu⟩ := hc.map [q, q] s s j j (by rw [hw]; rfl) t
  let i := typeF4RootPairing_baseEquiv.symm q
  have hn : pairTransportNodes i j [true, true] = [q, q] := by
    simp [pairTransportNodes, pairNode, i, sourceIndex]
  have he : pairEvaluation F i j (pairTransportTitsWord F [true, true]) =
      titsEvaluation F [q, q] := by rw [pair_titsEvaluation, hn]
  refine ⟨u, ?_⟩
  have hp := NormalizerTransportPath.localStep (F := F) i j [true, true]
    s false s false t u (by simpa only [he, pairNode, Bool.false_eq_true, ite_false] using hu)
  simpa only [he, pairNode, Bool.false_eq_true, ite_false] using hp

/-- The entire square correction acts by local paths, preserving the signed
simple root and retaining every actual change of parameter. -/
theorem path_squares (hc : SimpleTransport F) (d : List Node)
    (s : Bool) (j : Fin 4) (t : F) :
    ∃ u : F, NormalizerTransportPath F (titsEvaluation F (squareWord d))
      (s, j, t) (s, j, u) := by
  induction d generalizing t with
  | nil =>
    refine ⟨t, ?_⟩
    rw [squareWord_nil, titsEvaluation_nil]
    exact NormalizerTransportPath.refl (F := F) _
  | cons q d ih =>
    obtain ⟨u, hu⟩ := ih t
    obtain ⟨v, hv⟩ := path_square F hc q s j u
    refine ⟨v, ?_⟩
    rw [squareWord_cons, titsEvaluation_append]
    exact NormalizerTransportPath.trans hu hv

/-- Conditional assembly into the exact matrix path required by normalizer
coherence. The geometric, operator, and square-correction inputs remain open. -/
theorem hasNormalizerTransportPaths_of_inputs [Finite F]
    (hg : HasWeylPairPaths) (hc : SimpleTransport F) (ht : HasSquareCorrections F) :
    HasNormalizerTransportPaths F := by
  intro n hn s z i j t u hne he
  obtain ⟨w, rfl⟩ := exists_positive_word F hn
  have hw := hc.recognize w s z i j t u hne he
  obtain ⟨v, hv, a, ha⟩ := lift_weyl_path F hc (hg w s z i j hw) t
  obtain ⟨d, hd⟩ := ht w v hv.symm
  obtain ⟨b, hb⟩ := path_squares F hc d z j a
  have hp : NormalizerTransportPath F (titsEvaluation F w) (s, i, t) (z, j, b) := by
    rw [hd]
    exact NormalizerTransportPath.trans ha hb
  have hu : coverSimple F z j b = coverSimple F z j u :=
    (path_conjugates F hp).symm.trans he
  have hlast := path_of_element_eq F z z j j b u hu
  simpa only [one_mul] using NormalizerTransportPath.trans hp hlast

/-- Application to the existing coherence consumer. Restricted normalizer
faithfulness belongs to its independent producer. -/
theorem transportCoherent_of_inputs [Finite F]
    (hf : TransportNormalizerFaithful F)
    (hg : HasWeylPairPaths) (hc : SimpleTransport F) (ht : HasSquareCorrections F) :
    TransportCoherent F :=
  transportCoherent_of_normalizerFaithful_and_paths F hf
    (hasNormalizerTransportPaths_of_inputs F hg hc ht)

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
