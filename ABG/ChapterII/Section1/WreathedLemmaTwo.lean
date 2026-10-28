module
public import ABG.ChapterII.Section1.WreathedBaseStructure
public import ABG.ChapterII.Section1.WreathedFourSubgroups
public import ABG.ChapterII.Section1.WreathedQuaternionUnique
public import ABG.ChapterII.Section1.WreathedDerived
public import ABG.ChapterII.Section1.WreathedCentralQuotient
public import ABG.ChapterII.Section1.WreathedOmega
public import ABG.ChapterII.Section1.WreathedNormalClosure
public import ABG.ChapterII.Section1.WreathedOvergroups
public import ABG.ChapterII.Section1.WreathedNonabelianCenter
public import Theory.GroupTheory.PGroup.Omega
public import ABG.ChapterII.Section1.WreathedInvariantSubgroups

/-!
# ABG Chapter II, Section 1, Lemma 2

All thirteen structural clauses for a wreathed two-group, tied to the same
chosen generators and height n ≥ 2. The notation on article p.9 is retained:
x denotes x₁, the half-power of u. The statement includes all element and
subgroup conjugacy assertions, both uniqueness assertions, the derived and
center identifications, omega and quotient structure, the normal closure and
generator change, and the final three subgroup restrictions.

Unique coordinates identify the abelian base and involutions. Explicit
quaternion relations and the outside order-four calculation identify Y and
prove its uniqueness. Coordinate centralizers identify the center and constrain
nonabelian subgroup centers; quotient presentations give the dihedral and cyclic
quotients. Cyclic two-subgroup structure handles proper overgroups of Y. For
the final invariant-subgroup clause, every noncyclic subgroup contains x;
disjointness forces the normalizing cyclic subgroup into the base, and an
injective commutator construction fills the prescribed ambient cardinality.
This module combines these independently proved results.

Source: Lemma 2 on article pp.9–10, `page-010.tex` and `page-011.tex` of the
ABG transcription. Clause (iii) uses the scan-corrected Ω₁(U), embedded in S.
The proper overgroup in clause (xi) strictly contains Y. Products are written
as subgroup joins: normality justifies TY, centralization justifies YZ(X),
and the stated invariance makes XA a subgroup in clause (xiii).
-/

namespace ABG.Wreathed
variable {S : Type*} [Group S] {n : ℕ}

/-- The thirteen source clauses attached to the chosen presentation. -/
public structure LemmaTwoConclusion (P : Presentation S n) : Prop where
  part_i :
    orderOf P.x = 2 ∧ orderOf P.x₂ = 2 ∧ orderOf P.z = 2 ∧
      ¬ IsConj P.x P.x₂ ∧ ¬ IsConj P.x P.z ∧ ¬ IsConj P.x₂ P.z ∧
      ∀ g : S, orderOf g = 2 → IsConj g P.x ∨ IsConj g P.x₂ ∨ IsConj g P.z
  part_ii :
    IsMulCommutative P.U ∧ IsCoatom P.U ∧
      Nonempty (P.U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) ∧
      ∀ V : Subgroup S, IsMulCommutative V → Nat.card V = Nat.card P.U → V = P.U
  part_iii :
    P.T = (omega₁ P.U (p := 2)).map P.U.subtype ∧ IsKleinFour P.T ∧ P.T.Normal
  part_iv :
    IsKleinFour P.T₀ ∧
      (¬ ∃ g : S, P.T.map (MulAut.conj g).toMonoidHom = P.T₀) ∧
      ∀ V : Subgroup S, IsKleinFour V → V ≠ P.T →
        ∃ g : S, P.T₀.map (MulAut.conj g).toMonoidHom = V
  part_v :
    IsGeneralizedQuaternionGroup P.Y ∧ Nat.card P.Y = 2 ^ (n + 1) ∧ P.Y.Normal ∧
      ∀ Q : Subgroup S, IsGeneralizedQuaternionGroup Q → Nat.card Q = 2 ^ (n + 1) → Q = P.Y
  part_vi :
    commutator S = Subgroup.zpowers P.r ∧ IsCyclic (commutator S) ∧
      Nat.card (commutator S) = 2 ^ n
  part_vii :
    Subgroup.center S = Subgroup.zpowers P.u ∧ IsCyclic (Subgroup.center S) ∧
      Nat.card (Subgroup.center S) = 2 ^ n ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* DihedralGroup (2 ^ n))
  part_viii :
    letI : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
    omega₁ S (p := 2) = P.T ⊔ P.Y ∧ IsCyclic (S ⧸ omega₁ S (p := 2))
  part_ix : Subgroup.normalClosure (Subgroup.zpowers P.d : Set S) = P.Y
  part_x : (P.s * P.z) ^ 2 = P.u ∧ P.Y ⊔ Subgroup.zpowers (P.s * P.z) = ⊤
  part_xi :
    ∀ X : Subgroup S, X < ⊤ → P.Y < X →
      X = P.Y ⊔ (Subgroup.center X).map X.subtype ∧ P.T ≤ X
  part_xii :
    ∀ X : Subgroup S, ¬ IsMulCommutative X →
      (Subgroup.center X).map X.subtype ≤ Subgroup.center S
  part_xiii :
    ∀ X A : Subgroup S, IsCyclic A → Nat.card A = 2 ^ n →
      A ≤ Subgroup.normalizer (X : Set S) → Disjoint A X →
        IsCyclic X ∨ X ⊔ A = ⊤

/-- All thirteen source clauses for one chosen wreathed presentation. -/
public theorem lemma_two_of_presentation (P : Presentation S n) : LemmaTwoConclusion P := by
  have h2 := P.base_structure
  have h5 := P.quaternion_subgroup
  have h7 := P.center_structure
  exact {
    part_i := P.involution_classes
    part_ii := ⟨h2.2.2.1, h2.2.2.2.1, h2.1, fun V hV hcard =>
      h2.2.2.2.2 V hV (hcard.trans h2.2.1)⟩
    part_iii := P.base_four_structure
    part_iv := P.four_subgroup_classes
    part_v := ⟨h5.1, h5.2.1, h5.2.2, fun Q hQ hc => P.quaternion_unique Q hQ hc⟩
    part_vi := P.derived_structure
    part_vii := ⟨h7.1, h7.2.1, h7.2.2, P.central_quotient_equiv⟩
    part_viii := P.omega_structure
    part_ix := P.normal_closure_d
    part_x := P.generator_change
    part_xi := P.proper_overgroup
    part_xii := P.nonabelian_center_le
    part_xiii := fun X A hA hc hn hd => by
      let : IsCyclic A := hA
      exact P.invariant_disjoint_cyclic X A hc hn hd }

/-- The complete structure lemma at a specified wreathed height. -/
public theorem lemma_two_of_height (hS : IsWreathedOfHeight S n) :
    ∃ P : Presentation S n, LemmaTwoConclusion P := by
  obtain ⟨P⟩ := nonempty_presentation hS
  exact ⟨P, lemma_two_of_presentation P⟩

/-- ABG Chapter II, Section 1, Lemma 2, with all thirteen clauses. -/
public theorem lemma_two (hS : IsWreathedGroup S) :
    ∃ (n : ℕ) (P : Presentation S n), LemmaTwoConclusion P := by
  obtain ⟨n, hn⟩ := hS
  obtain ⟨P, hP⟩ := lemma_two_of_height hn
  exact ⟨n, P, hP⟩

end ABG.Wreathed
