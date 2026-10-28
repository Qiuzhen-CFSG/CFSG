module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Theory.AlgebraicGroup.Automorphisms.SteinbergCore
public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_2
public import Theory.AlgebraicGroup.Bor1.TangentDimension

/-!
Geometric power classification for a Frobenius generator.

The algebraic input is one regular Steinberg realization of the generator,
nilpotence of its identity differential, and finite fixed loci for its positive
iterates.  These are independent geometric consequences of the Steinberg
fixed-locus criterion; none asserts the desired integral-power equivalences.
Iteration supplies regular morphisms and surjectivity for nonnegative powers.
The nilpotent differential rules out an algebraic inverse of every positive
power, while the finite fixed-locus input supplies the Steinberg membership.
-/

universe u

namespace Theory.AlgebraicGroup

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

private def endomorphismIterate
    {K : Variety k} [AlgebraicGroup K]
    (f : AlgebraicEndomorphism K) : Nat -> AlgebraicEndomorphism K
  | 0 => AlgebraicGroup.Morphism.id K
  | n + 1 => (endomorphismIterate f n).comp f

private lemma endomorphismIterate_onPoints
    {K : Variety k} [AlgebraicGroup K]
    (f : AlgebraicEndomorphism K) (n : Nat) :
    (endomorphismIterate f n).onPoints = f.onPoints^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext x
      change (endomorphismIterate f n).onPoints (f.onPoints x) = _
      rw [ih]
      rfl

private lemma iterate_realizes_zpow
    {K : Variety k} [AlgebraicGroup K]
    (g : Aut K) (f : AlgebraicEndomorphism K)
    (hgf : IsAlgebraicRealization g f) :
    forall n : Nat,
      IsAlgebraicRealization (g ^ (n : Int)) (endomorphismIterate f n) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      change (g ^ (n : Int)) (g x) = _
      rw [show g x = f.onPoints x from hgf x, <- ih]
      rfl

private lemma nilpotent_injective_linearMap_forces_subsingleton
    {V : Type u} [AddCommGroup V] [Module k V]
    (L : V ->ₗ[k] V) (hL : IsNilpotent L)
    (hinj : Function.Injective L) : Subsingleton V := by
  obtain ⟨n, hn⟩ := hL
  have hpow_inj : forall m : Nat, Function.Injective (L ^ m) := by
    intro m
    induction m with
    | zero =>
        intro x y h
        exact h
    | succ m ih =>
        intro x y h
        apply ih
        apply hinj
        simpa [pow_succ, LinearMap.comp_apply] using h
  constructor
  intro x y
  apply hpow_inj n
  rw [hn]
  simp

private lemma simple_identityTangent_nontrivial
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSimpleAlgebraicGroup K) : Nontrivial (IdentityPointDerivation K) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  letI : Subsingleton (IdentityPointDerivation K) := hsub
  have hfinrank : Module.finrank k (IdentityPointDerivation K) = 0 :=
    finrank_zero_iff_forall_zero.mpr (fun D => Subsingleton.elim D 0)
  have hdimNat : Cardinal.toNat (Variety.dimension K) = 0 := by
    rw [<- identityPointDerivation_finrank_eq_dimension]
    exact hfinrank
  have hdim : Variety.dimension K = 0 := by
    rcases Cardinal.toNat_eq_zero.mp hdimNat with hzero | hinfinite
    · exact hzero
    · exact False.elim
        ((not_le_of_gt (variety_dimension_lt_aleph0 K)) hinfinite)
  have hfinite : Finite (Variety.Point K) :=
    (dimension_zero_iff_finite_points K).mp hdim
  let : T1Space (Variety.Point K) :=
    ⟨fun x => Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton K x)⟩
  have hnontrivial : Nontrivial (Variety.Point K) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsubsingleton
    letI : Subsingleton (Variety.Point K) := hsubsingleton
    exact hK.2.1 (Subsingleton.elim _ _)
  exact hfinite.not_infinite
    (hK.1.isPreconnected.infinite_of_nontrivial hnontrivial)

private lemma not_algebraic_realization_negSucc
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSimpleAlgebraicGroup K)
    (g : Aut K) (f : AlgebraicEndomorphism K)
    (hgf : IsAlgebraicRealization g f)
    (hNilpotent : IsNilpotent (identityTangentMorphismLinearMap f))
    (n : Nat) :
    not HasAlgebraicEndomorphismRealization (g ^ (-[n + 1] : Int)) := by
  rintro ⟨q, hq⟩
  let p := endomorphismIterate f (n + 1)
  have hp : IsAlgebraicRealization (g ^ ((n + 1 : Nat) : Int)) p :=
    iterate_realizes_zpow g f hgf (n + 1)
  have hqp : forall x, q.onPoints (p.onPoints x) = x := by
    intro x
    rw [<- hq, <- hp]
    simp
  have hpq : forall x, p.onPoints (q.onPoints x) = x := by
    intro x
    rw [<- hp, <- hq]
    simp
  let e : AlgebraicGroup.Iso K K :=
    AlgebraicGroup.Iso.ofInverseMorphisms p q hqp hpq
  have hdiff_p :
      identityTangentMorphismLinearMap p =
        identityTangentMorphismLinearMap f ^ (n + 1) := by
    induction n with
    | zero =>
        simp [p, endomorphismIterate]
    | succ n ih =>
        change identityTangentMorphismLinearMap
          ((endomorphismIterate f (n + 1)).comp f) = _
        rw [identityTangentMorphismLinearMap_comp]
        change _ = identityTangentMorphismLinearMap f ^ (n + 1 + 1)
        rw [show identityTangentMorphismLinearMap (endomorphismIterate f (n + 1)) =
            identityTangentMorphismLinearMap f ^ (n + 1) from ih, pow_succ]
  have hNilpotentP : IsNilpotent (identityTangentMorphismLinearMap p) := by
    rw [hdiff_p]
    exact hNilpotent.pow (n + 1)
  have hcomp : e.inv.comp e.hom = AlgebraicGroup.Morphism.id K := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact e.hom_inv_id x
  have hleft :
      (identityTangentMorphismLinearMap e.inv).comp
          (identityTangentMorphismLinearMap p) = LinearMap.id := by
    rw [show p = e.hom from rfl, <- identityTangentMorphismLinearMap_comp,
      hcomp, identityTangentMorphismLinearMap_id]
  have hinj : Function.Injective (identityTangentMorphismLinearMap p) := by
    apply Function.LeftInverse.injective
    intro D
    exact LinearMap.congr_fun hleft D
  have hsub := nilpotent_injective_linearMap_forces_subsingleton
    (identityTangentMorphismLinearMap p) hNilpotentP hinj
  exact not_subsingleton_iff_nontrivial.mpr
    (simple_identityTangent_nontrivial hK) hsub

/-- Classify all integral powers once the independent geometric inputs for the
generator have been supplied. -/
public theorem frobeniusPower_geometric_classification
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSimpleAlgebraicGroup K)
    (g : Aut K) (f : AlgebraicEndomorphism K)
    (hgf : IsAlgebraicRealization g f)
    (hf : IsAlgebraicSteinbergEndomorphism f)
    (hNilpotent : IsNilpotent (identityTangentMorphismLinearMap f))
    (hpositiveFixed : forall n : Nat, 0 < n ->
      Finite {x : Variety.Point K | f.onPoints^[n] x = x}) :
    (forall a : Int,
      HasAlgebraicEndomorphismRealization (g ^ a) <-> 0 <= a) /\
    (forall a : Int, g ^ a ∈ SteinbergAutomorphismSet K <-> 0 < a) := by
  constructor
  · intro a
    constructor
    · intro ha
      rcases a with (n | n)
      · omega
      · exact False.elim (not_algebraic_realization_negSucc hK g f hgf hNilpotent n ha)
    · intro ha
      rcases a with (n | n)
      · exact ⟨endomorphismIterate f n, iterate_realizes_zpow g f hgf n⟩
      · omega
  · intro a
    constructor
    · rintro ⟨q, hq, hqSteinberg⟩
      by_contra hnot
      have hle : a <= 0 := le_of_not_gt hnot
      rcases a with (n | n)
      · have hn : n = 0 := by omega
        subst n
        have hfixed : Finite {x : Variety.Point K | q.onPoints x = x} := hqSteinberg.2
        have hall : {x : Variety.Point K | q.onPoints x = x} = Set.univ := by
          ext x
          simp [<- hq]
        rw [hall] at hfixed
        let : T1Space (Variety.Point K) :=
          ⟨fun x => Variety.isClosed_iff_isZariskiClosed.mpr
            (isZariskiClosed_singleton K x)⟩
        have hnontrivial : Nontrivial (Variety.Point K) := by
          apply not_subsingleton_iff_nontrivial.mp
          intro hsubsingleton
          letI : Subsingleton (Variety.Point K) := hsubsingleton
          exact hK.2.1 (Subsingleton.elim _ _)
        exact hfixed.not_infinite
          (hK.1.isPreconnected.infinite_of_nontrivial hnontrivial)
      · exact False.elim (not_algebraic_realization_negSucc hK g f hgf hNilpotent n ⟨q, hq⟩)
    · intro ha
      obtain ⟨n, hn, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt ha)
      have hnpos : 0 < n := by omega
      let p := endomorphismIterate f n
      refine mem_steinbergAutomorphismSet_of_realization
        (iterate_realizes_zpow g f hgf n) ⟨?_, ?_⟩
      · rw [endomorphismIterate_onPoints]
        exact hf.1.iterate n
      · rw [endomorphismIterate_onPoints]
        exact hpositiveFixed n hnpos

end Theory.AlgebraicGroup
