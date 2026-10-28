module

public import CFSG.Quasithin.Chapter16.Defs
public import CFSG.Quasithin.Chapter16.Section01To02.Local
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Mathlib.GroupTheory.Frattini

/-!
# The QTK even-type hypothesis

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, Hypothesis 16.1.1 and conditions (E1)–(E2), pp.1169–1170.
The book states even type for QTK-groups by the following centralizer conditions,
without requiring two-rank at least three. These definitions encode that version;
they do not assert an equivalence for arbitrary groups with the GLS definition.

All model alternatives use the concrete carriers of Theorem C. The quotient
is by O₂(L), not by the center or the two-residual. The exclusions concern
the full covering group L. The notation A₈/Z₂ is a double central cover of A₈:
it is represented by a central quotient isomorphism and center of order two,
under the surrounding component (hence quasisimplicity) hypothesis.

The local SQTK deduction uses only quasithinness, nonabelian simplicity and
proper-K. In particular it does not require even characteristic, which is
explicitly excluded by this chapter's standing hypothesis.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16

open Subgroup Theory.GroupTheory ClassificationModels ChapterA.Section02

universe u

/-- The full SL₂(q) cover, with an actual matrix-group isomorphism. -/
def IsSLTwoAt (L : Type u) [Group L] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F)

/-- The double central covering type A₈/Z₂ excluded in (E2)(i).
The surrounding use requires L to be quasisimple. -/
def IsDoubleCentralCoverOfA8 (L : Type u) [Group L] : Prop :=
  Nat.card (center L) = 2 ∧
    Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 8))

/-- Exactly the characteristic-two alternatives C(3)–C(4). -/
def IsEvenTypeLieQuotient (S : Type u) [Group S] : Prop :=
  IsBenderModel S ∨ (∃ f : ℕ, IsTheoremCRankTwoModel S f) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL S n 2)

/-- Condition (E2)(i), including its covering and Frattini restrictions. -/
def IsEvenTypeLieComponent (L : Type u) [Group L] : Prop :=
  IsEvenTypeLieQuotient (L ⧸ pCore 2 L) ∧
    (∀ q : ℕ, q = 5 ∨ q = 7 ∨ q = 9 → ¬ IsSLTwoAt L q) ∧
    ¬ IsDoubleCentralCoverOfA8 L ∧
    (ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 → frattini (pCore 2 L) = ⊥)

/-- Exactly the nine sporadics in (E2)(iii), excluding J₁, J₃ and He. -/
def IsEvenTypeSporadicQuotient (S : Type u) [Group S] : Prop :=
  ∃ name : SporadicName, name ≠ .j3 ∧ name ≠ .he ∧ Nonempty (S ≃* name.Carrier)

/-- All three alternatives of (E2). The odd-characteristic clause describes L
itself, while the characteristic-two and sporadic clauses describe L/O₂(L). -/
def IsEvenTypeComponent (L : Type u) [Group L] : Prop :=
  IsEvenTypeLieComponent L ∨ ClassicalGroup.IsPSL L 3 3 ∨
    (∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
    IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L)

/-- The source's QTK version of even type, namely (E1) and (E2).
This is a hypothesis, not a classification theorem. -/
structure HasEvenTypeCentralizers (G : Type u) [Group G] : Prop where
  oddCore : ∀ t : G, orderOf t = 2 → pPrimeCore 2 (involutionCentralizer t) = ⊥
  components : ∀ (t : G) (L : Subgroup G), orderOf t = 2 →
    IsCentralizerComponent t L → IsEvenTypeComponent L

/-- Hypothesis 16.1.1, with the shared proper-K induction input explicit. -/
structure Hypothesis1611 (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonabelian : ¬ IsMulCommutative G
  quasithin : IsQuasithin G
  properK : HasProperKSubgroups K G
  not_evenCharacteristic : ¬ IsEvenCharacteristic G
  evenType : HasEvenTypeCentralizers G

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The SQTK input to A.3 and I.3 is available without even characteristic. -/
theorem Hypothesis1611.involution_centralizer_sqtk
    (h : Hypothesis1611 K G) {t : G} (ht : orderOf t = 2) :
    IsSQTK K (involutionCentralizer t) := by
  let := h.simple
  have hlocal := isTwoLocal_involution_centralizer ht
  exact ⟨isQuasithin_iff_twoLocal.mp h.quasithin _ hlocal,
    h.properK _ (twoLocal_ne_top_of_nonabelian_simple h.nonabelian hlocal)⟩

/-- The catalogue-independent equality in 16.1.2(1), proved from (E1).
It holds for simple components as well as for the nonsimple ones listed there. -/
theorem HasEvenTypeCentralizers.component_center_eq_twoCore
    (h : HasEvenTypeCentralizers G) {t : G} (ht : orderOf t = 2)
    {L : Subgroup G} (hL : IsCentralizerComponent t L) :
    center L = pCore 2 L := by
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot (h.oddCore t ht)
    (L.subgroupOf (involutionCentralizer t)) hL.2.1
  have hmap := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
  have hLcore : pPrimeCore 2 L = ⊥ := by
    simpa only [hcore, Subgroup.map_bot] using hmap.symm
  let := hL.quasisimple
  exact IsQuasisimple.center_eq_pCore hLcore

end CFSG.Quasithin.Chapter16
