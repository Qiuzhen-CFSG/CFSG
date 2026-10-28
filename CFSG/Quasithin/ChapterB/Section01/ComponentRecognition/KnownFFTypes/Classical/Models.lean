module

public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Concrete outputs for the classical branch of B.1.13

The field parameter is retained in all six classical catalogue rows.
In characteristic two, the covering-group output uses actual central
quotients of SL and SU and the actual projective symplectic and orthogonal
carriers. In particular, an isomorphism of simple central quotients is not
an identification of the original covering group.

The additional derived G₂(2) carrier retains the exceptional odd-field
unitary possibility PSU₃(3). Source Remark B.4.4 explicitly counts this
group as characteristic two. Its identification requires an actual
isomorphism of the whole covering group, just as in the classical rows.

These definitions are shared by the classical FF exclusions and the
independent covering calculations. They do not assert the classification.
The alternative alternating output identifies the simple central quotient,
as required before the separate alternating-cover argument in B.1.13.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, B.1.13, printed pp.73–74; classical
parameter conventions are those of `CFSG.KnownSimple.ClassicalModels`.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical

universe u v

/-- The complete classical catalogue with its original field parameter visible. -/
inductive IsClassicalAt (G : Type u) [Group G] (q : ℕ) : Prop
  | linear (n : ℕ) (parameters : KnownSimple.LinearParameters n q)
      (iso : ClassicalGroup.IsPSL G n q)
  | unitary (n : ℕ) (parameters : KnownSimple.UnitaryParameters n q)
      (iso : ClassicalGroup.IsPSU G n q)
  | symplectic (r : ℕ) (parameters : KnownSimple.SymplecticParameters r q)
      (iso : ClassicalGroup.IsPSp G r q)
  | orthogonalPlus (r : ℕ) (parameters : KnownSimple.OrthogonalPlusParameters r q)
      (iso : ClassicalGroup.IsPOmegaPlus G r q)
  | orthogonalOdd (r : ℕ) (parameters : KnownSimple.OrthogonalOddParameters r q)
      (iso : ClassicalGroup.IsPOmegaOdd G r q)
  | orthogonalMinus (r : ℕ) (parameters : KnownSimple.OrthogonalMinusParameters r q)
      (iso : ClassicalGroup.IsPOmegaMinus G r q)

/-- Exposing the field parameter loses none of the six catalogue constructors. -/
theorem isClassicalModel_iff_exists_parameter (G : Type u) [Group G] :
    KnownSimple.IsClassicalModel G ↔ ∃ q, IsClassicalAt G q := by
  constructor
  · intro h
    cases h with
    | linear n q hp hi => exact ⟨q, .linear n hp hi⟩
    | unitary n q hp hi => exact ⟨q, .unitary n hp hi⟩
    | symplectic r q hp hi => exact ⟨q, .symplectic r hp hi⟩
    | orthogonalPlus r q hp hi => exact ⟨q, .orthogonalPlus r hp hi⟩
    | orthogonalOdd r q hp hi => exact ⟨q, .orthogonalOdd r hp hi⟩
    | orthogonalMinus r q hp hi => exact ⟨q, .orthogonalMinus r hp hi⟩
  · rintro ⟨q, h⟩
    cases h with
    | linear n hp hi => exact .linear n q hp hi
    | unitary n hp hi => exact .unitary n q hp hi
    | symplectic r hp hi => exact .symplectic r q hp hi
    | orthogonalPlus r hp hi => exact .orthogonalPlus r q hp hi
    | orthogonalOdd r hp hi => exact .orthogonalOdd r q hp hi
    | orthogonalMinus r hp hi => exact .orthogonalMinus r q hp hi

/-- An actual quotient by a central subgroup of the displayed concrete group.
Normality is included to specify the literal Lean quotient instance. -/
def IsCentralQuotient (G : Type u) [Group G] (H : Type v) [Group H] : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), N ≤ center H ∧ Nonempty (G ≃* H ⧸ N)

/-- The whole group, not just its simple quotient, has a concrete even
classical model. The SL and SU rows permit their genuine central quotients. -/
inductive IsEvenClassicalGroup (G : Type u) [Group G] : Prop
  | linear (n q : ℕ) (parameters : KnownSimple.LinearParameters n q) (even : Even q)
      (F : Type) [Field F] [Finite F] (card : Nat.card F = q)
      (iso : IsCentralQuotient G SL(n, F))
  | unitary (n q : ℕ) (parameters : KnownSimple.UnitaryParameters n q) (even : Even q)
      (F : Type) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm n F)
      (card : Nat.card F = q ^ 2) (conj : ∀ x, J.conj x = x ^ q)
      (iso : IsCentralQuotient G J.specialSubgroup)
  | symplectic (r q : ℕ) (parameters : KnownSimple.SymplecticParameters r q) (even : Even q)
      (iso : ClassicalGroup.IsPSp G r q)
  | orthogonalPlus (r q : ℕ) (parameters : KnownSimple.OrthogonalPlusParameters r q)
      (even : Even q) (iso : ClassicalGroup.IsPOmegaPlus G r q)
  | orthogonalOdd (r q : ℕ) (parameters : KnownSimple.OrthogonalOddParameters r q)
      (even : Even q) (iso : ClassicalGroup.IsPOmegaOdd G r q)
  | orthogonalMinus (r q : ℕ) (parameters : KnownSimple.OrthogonalMinusParameters r q)
      (even : Even q) (iso : ClassicalGroup.IsPOmegaMinus G r q)

/-- Projective models themselves are particular concrete central quotients. -/
theorem IsClassicalAt.isEvenClassicalGroup {G : Type u} [Group G] {q : ℕ}
    (h : IsClassicalAt G q) (he : Even q) : IsEvenClassicalGroup G := by
  cases h with
  | linear n hp hi =>
    obtain ⟨F, hF, hfin, hc, e⟩ := hi
    exact .linear n q hp he F hc ⟨center SL(n, F), inferInstance, le_rfl, e⟩
  | unitary n hp hi =>
    obtain ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩ := hi
    let f := Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup
    have hk : f.ker ≤ center J.specialSubgroup := by
      intro A hA
      have hz : A.val ∈ center (GL (Fin n) F) :=
        Matrix.ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hA)
      exact mem_center_iff.mpr fun B => Subtype.ext (mem_center_iff.mp hz B.val)
    exact .unitary n q hp he F J hc hj
      ⟨f.ker, inferInstance, hk,
        ⟨e.trans (QuotientGroup.quotientKerEquivOfSurjective f
          (MonoidHom.subgroupMap_surjective _ _)).symm⟩⟩
  | symplectic r hp hi => exact .symplectic r q hp he hi
  | orthogonalPlus r hp hi => exact .orthogonalPlus r q hp he hi
  | orthogonalOdd r hp hi => exact .orthogonalOdd r q hp he hi
  | orthogonalMinus r hp hi => exact .orthogonalMinus r q hp he hi

/-- Characteristic-two Lie carriers needed for a classical simple quotient,
including the exceptional PSU₃(3) alias from source Remark B.4.4. -/
inductive IsEvenLieGroup (L : Type u) [Group L] : Prop
  | classical (model : IsEvenClassicalGroup L)
  | g2Derived (iso : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- Recognition of a simple quotient, retaining its actual characteristic-two
carrier. Lifting this to `IsEvenLieGroup L` is a separate covering theorem. -/
inductive IsEvenLieQuotient (S : Type u) [Group S] : Prop
  | classical (q : ℕ) (even : Even q) (model : IsClassicalAt S q)
  | g2Derived (iso : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- The output of the odd-characteristic representation exclusions, before
the independent covering theorem identifies the whole original group. -/
def QuotientAlternative (L : Type u) [Group L] : Prop :=
  IsEvenLieQuotient (L ⧸ center L) ∨
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin m))

/-- The covering group is of characteristic-two Lie type, or its simple
central quotient is an alternating group of degree at least five. -/
def Conclusion (L : Type u) [Group L] : Prop :=
  IsEvenLieGroup L ∨
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin m))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
