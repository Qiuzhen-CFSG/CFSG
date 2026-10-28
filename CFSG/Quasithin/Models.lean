module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ClassificationModels
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.FermatMersenne
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.Mathieu.M11.Basic
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.Mathieu.M23.Basic
public import Theory.Mathieu.M24.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.SpecificGroups.Tits.Presentation

/-!
# Concrete models in the quasithin classification

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2 (printed p.4), its repeated statement on
p.482, Remark A.2.4, and the final proof on p.1166.

This module re-exports `ClassificationModels.IsQTKEModel`, the complete
actual-isomorphism output, and `KnownSimple.IsKnownSimple`, the full class K.
The former contains the generic Lie families, all the exceptional alternatives,
and the eleven sporadic outputs. The latter also contains prime cyclic groups,
all alternating simple groups, all finite simple Lie families, and all
twenty-six sporadics. `ClassificationModels.IsEvenTypeModel` adds J₁ to the
Main Theorem output.

The earlier `IsConstructedQTKEModel` remains unchanged as an explicitly partial
list. Its inclusion in the complete output is proved in
`ClassificationModels.ConstructedInclusion`; the inclusion of both lists in
the full K catalogue is in `KnownSimple.CarrierCatalogue.ClassificationInclusion`.
These extensions import this module, so they are not imported back here.

The guard bridges below instantiate the source hypotheses with the full K
catalogue. Every simple section of a finite group is already finite and simple,
so its finite-simple guard leaves SQTK, QTKE, and simple QTKE unchanged. These
are interface equivalences, not the forward or converse classification theorem.
In particular membership in the output list does not supply proper K or E.

The rank in the source is the relative (BN-pair) rank. Thus both `PSU₄(q)` and
`PSU₅(q)` have rank two. The latter occurs only at `q = 4`, so its defining
matrices have coefficients in a field of order 16, not 4. The notation
`Lₙ^ε(3)` on p.4 includes both `PSLₙ(3)` and `PSUₙ(3)`.

The complete output includes the actual commutator carriers `Sp₄(2)'` and
`G₂(2)'`, and uses `Tits.ParrottGroup` for `²F₄(2)'`. The earlier partial list
contains `A₆` and `PSU₃(3)`, their conventional isomorphic alternatives; no
comparison isomorphism between these different carriers is asserted here.
The full nonsimple groups at these parameters are excluded.
The overlaps `PSL₂(4) ≅ A₅` and `PSL₄(2) ≅ A₈` are intentionally retained,
just as in the source. Every model witness below is a multiplicative equivalence;
no group is defined from quasithinness or the classification predicate.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin

/-- The five concrete Mathieu models. -/
def IsMathieuModel (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* Sporadic.Mathieu.M11) ∨
  Nonempty (G ≃* Sporadic.Mathieu.M12) ∨
  Nonempty (G ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (G ≃* Sporadic.Mathieu.M23) ∨
  Nonempty (G ≃* Sporadic.Mathieu.M24)

/-- The already constructed alternatives of the QTKE conclusion. This is an
intermediate sublist, not the final classification predicate or the class `K`. -/
inductive IsConstructedQTKEModel (G : Type u) [Group G] : Prop
  | alternating (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9)
      (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | linear_even (n f : ℕ)
      (parameters : (n = 2 ∧ 2 ≤ f) ∨ (n = 3 ∧ 1 ≤ f) ∨
        ((n = 4 ∨ n = 5) ∧ f = 1))
      (iso : ClassicalGroup.IsPSL G n (2 ^ f))
  | unitary_even (n f : ℕ)
      (parameters : (n = 3 ∧ 2 ≤ f) ∨ (n = 4 ∧ 1 ≤ f) ∨ (n = 5 ∧ f = 2))
      (iso : ClassicalGroup.IsPSU G n (2 ^ f))
  | symplectic_even (r f : ℕ)
      (parameters : (r = 2 ∧ 2 ≤ f) ∨ (r = 3 ∧ f = 1))
      (iso : ClassicalGroup.IsPSp G r (2 ^ f))
  | linear_prime (p : ℕ) (hp : IsFermatOrMersennePrime p) (large : 5 ≤ p)
      (iso : ClassicalGroup.IsPSL G 2 p)
  | linear_three (n : ℕ) (hn : n = 3 ∨ n = 4)
      (iso : ClassicalGroup.IsPSL G n 3)
  | unitary_three (n : ℕ) (hn : n = 3 ∨ n = 4)
      (iso : ClassicalGroup.IsPSU G n 3)
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | mathieu (iso : IsMathieuModel G)
  | tits (iso : Nonempty (G ≃* Tits.ParrottGroup))

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The Mathieu alternatives depend only on the isomorphism type. -/
theorem IsMathieuModel.of_mulEquiv (h : IsMathieuModel G) (e : H ≃* G) :
    IsMathieuModel H := by
  unfold IsMathieuModel at h ⊢
  rcases h with f | f | f | f | f
  · exact Or.inl (f.map fun a => e.trans a)
  · exact Or.inr (Or.inl (f.map fun a => e.trans a))
  · exact Or.inr (Or.inr (Or.inl (f.map fun a => e.trans a)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (f.map fun a => e.trans a))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (f.map fun a => e.trans a))))

/-- All constructed alternatives transport by composing their actual model
isomorphisms. This also works across universe levels. -/
theorem IsConstructedQTKEModel.of_mulEquiv (h : IsConstructedQTKEModel G)
    (e : H ≃* G) : IsConstructedQTKEModel H := by
  cases h with
  | alternating n hn iso =>
      exact .alternating n hn (iso.map fun f => e.trans f)
  | linear_even n f hp iso => exact .linear_even n f hp (iso.of_mulEquiv e)
  | unitary_even n f hp iso => exact .unitary_even n f hp (iso.of_mulEquiv e)
  | symplectic_even r f hp iso => exact .symplectic_even r f hp (iso.of_mulEquiv e)
  | linear_prime p hp hlarge iso => exact .linear_prime p hp hlarge (iso.of_mulEquiv e)
  | linear_three n hn iso => exact .linear_three n hn (iso.of_mulEquiv e)
  | unitary_three n hn iso => exact .unitary_three n hn (iso.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun f => e.trans f)
  | mathieu iso => exact .mathieu (iso.of_mulEquiv e)
  | tits iso => exact .tits (iso.map fun f => e.trans f)

theorem isMathieuModel_mulEquiv_iff (e : G ≃* H) :
    IsMathieuModel G ↔ IsMathieuModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isConstructedQTKEModel_mulEquiv_iff (e : G ≃* H) :
    IsConstructedQTKEModel G ↔ IsConstructedQTKEModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- The full K catalogue can be used with or without its finite-simple guard
in the strongly quasithin local hypothesis. -/
theorem isSQTK_knownSimple_guard_iff [Finite G] :
    IsSQTK KnownSimple.IsKnownSimple G ↔
      IsSQTK KnownSimple.IsKnownSimpleCarrier G := by
  constructor
  · intro h
    exact ⟨h.stronglyQuasithin,
      (KnownSimple.isKGroup_knownSimple_guard_iff G).mp h.isKGroup⟩
  · intro h
    exact ⟨h.stronglyQuasithin,
      (KnownSimple.isKGroup_knownSimple_guard_iff G).mpr h.isKGroup⟩

/-- Guard removal preserves all three clauses of the Main Hypothesis, using
the full known-simple catalogue for its proper-subgroup clause. -/
theorem isQTKE_knownSimple_guard_iff [Finite G] :
    IsQTKE KnownSimple.IsKnownSimple G ↔
      IsQTKE KnownSimple.IsKnownSimpleCarrier G := by
  constructor
  · intro h
    exact ⟨h.quasithin,
      (KnownSimple.hasProperKSubgroups_knownSimple_guard_iff G).mp h.properK,
      h.evenCharacteristic⟩
  · intro h
    exact ⟨h.quasithin,
      (KnownSimple.hasProperKSubgroups_knownSimple_guard_iff G).mpr h.properK,
      h.evenCharacteristic⟩

/-- The same bridge in the finite nonabelian simple domain of Theorem 0.1.2.
It can be used in either direction of the eventual classification equivalence. -/
theorem isSimpleQTKE_knownSimple_guard_iff [Finite G] :
    IsSimpleQTKE KnownSimple.IsKnownSimple G ↔
      IsSimpleQTKE KnownSimple.IsKnownSimpleCarrier G := by
  constructor
  · intro h
    exact ⟨isQTKE_knownSimple_guard_iff.mp h.toIsQTKE, h.simple, h.nonabelian⟩
  · intro h
    exact ⟨isQTKE_knownSimple_guard_iff.mpr h.toIsQTKE, h.simple, h.nonabelian⟩

end CFSG.Quasithin
