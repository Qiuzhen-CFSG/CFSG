module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction

/-!
# The model conclusions of the proper enlargement alternatives

These predicates retain all nine model pairs in Aschbacher–Smith 16.1.7(3),
printed pp.1172–1173. They are the model projection of that earlier theorem,
not an assertion of it. The automorphism labels are not used by the covered
persistence argument. The ambient geometry, commutator equality and relative
component hypotheses remain explicit in `ProperModelInput`.

In (a), the smaller endpoint is the actual derived subgroup, including at
field order two. The family index ties both endpoints to the same Lie type.
In (b)–(i), the smaller endpoint is L itself, not L/O₂(L). In particular (d)
includes simple Sz(8); the sentence “only (i)” in the proof of 16.2.6 on p.1174
does not justify deleting (d). The field order for unitary groups is the
fixed-field order. Symplectic notation here is projective; in characteristic
two this is canonically the symplectic group in the source.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open Subgroup Theory.GroupTheory ClassificationModels ComponentTransfer
universe v

/-- The five Lie types allowed by (E2) and the exclusions in 16.1.7(3a). -/
inductive FieldFamily
  | linearTwo | linearThree | symplecticFour | g2 | triality

/-- Actual models for a fixed Lie type and field order. -/
def FieldFamily.ModelAt (X : FieldFamily) (M : Type*) [Group M] (q : ℕ) : Prop :=
  match X with
  | .linearTwo => ClassicalGroup.IsPSL M 2 q
  | .linearThree => ClassicalGroup.IsPSL M 3 q
  | .symplecticFour => ClassicalGroup.IsPSp M 2 q
  | .g2 => IsG2At M q
  | .triality => Triality.Standard.IsTrialityGroupAt q M

/-- X(q)′, with its genuine derived-subgroup carrier. -/
def FieldFamily.DerivedAt (X : FieldFamily) (S : Type v) [Group S] (q : ℕ) : Prop :=
  ∃ (M : Type) (_ : Group M) (_ : Finite M),
    X.ModelAt M q ∧ Nonempty (S ≃* commutator M)

/-- All nine model pairs, without any filtering by the covered Suzuki input. -/
inductive ProperModels (L J : Type v) [Group L] [Group J] : Prop
  | field (X : FieldFamily) (n : ℕ) (hn : 1 ≤ n)
      (large : X.ModelAt (J ⧸ pCore 2 J) (2 ^ (2 * n)))
      (small : X.DerivedAt (L ⧸ pCore 2 L) (2 ^ n))
  | graph_field_linear (n : ℕ) (hn : 1 < n)
      (large : ClassicalGroup.IsPSL J 3 (2 ^ (2 * n)))
      (small : ClassicalGroup.IsPSU L 3 (2 ^ n))
  | graph_linear_unitary (n : ℕ) (hn : 1 < n)
      (large : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ n) ∨
        ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ n))
      (small : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | graph_field_symplectic (m : ℕ) (hm : 1 ≤ m)
      (large : ClassicalGroup.IsPSp J 2 (2 ^ (2 * m + 1)))
      (small : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | graph_binary (n : ℕ) (hn : n = 4 ∨ n = 5)
      (large : ClassicalGroup.IsPSL J n 2)
      (small : Nonempty (L ≃* alternatingGroup (Fin 6)))
  | mathieu_janko
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M12) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier))
      (small : Nonempty (L ≃* alternatingGroup (Fin 5)))
  | janko_linear
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier))
      (small : ClassicalGroup.IsPSL L 3 2)
  | higman_sims
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.HS.Carrier))
      (small : Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (L ≃* alternatingGroup (Fin 8)))
  | rudvalis
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model))
      (small : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))

/-- The model projection of 16.1.7(3), an earlier source input. It asserts no
persistence, no non-enlargement, and no simplicity of an unspecified L. -/
def ProperModelInput (𝒦 : GroupClass.{v}) (G : Type v) [Group G] [Finite G] : Prop :=
  Hypothesis1611 𝒦 G → ∀ (s t : G) (L J : Subgroup G), Setup s t L →
    IsCentralizerComponent t J → ⁅J, zpowers s⁆ = J →
    IsComponentIn L (centralizerIn J s) → L < J → ProperModels L J

/-- The precise intrinsic comparison needed for a field-derived endpoint.
Only divisibility by three is requested, not its full order or simplicity. -/
def FieldDerivedThreeInput (X : FieldFamily) : Prop :=
  ∀ (M : Type) (_ : Group M) (_ : Finite M) (n : ℕ), 1 ≤ n →
    X.ModelAt M (2 ^ n) → 3 ∣ Nat.card (commutator M)

/-- The precise unitary comparison used for 16.1.7(3b). The coefficient
field has order q² and its involution is the q-power Frobenius. -/
def UnitaryThreeInput : Prop :=
  ∀ (F : Type) (_ : Field F) (_ : Finite F)
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (n : ℕ), 1 < n →
    Nat.card F = (2 ^ n) ^ 2 → (∀ x, J.conj x = x ^ (2 ^ n)) →
    3 ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence

end
