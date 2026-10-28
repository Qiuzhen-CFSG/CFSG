module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.ModelContracts
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import Theory.GroupTheory.CComponent.Basic

/-!
# The two source lists used in Lemma 16.2.5

A.3.8(3) applies to an SQTK-group with trivial two-core. Its nonnormal
C-component is one of four actual simple models, including J₁ and all
PSL₂(p) for primes p > 3. It does not yet impose the Fermat/Mersenne
restriction of (E2). In the application the ambient group is the quotient
of the involution centralizer by its two-core.

The nonsimple-cover list of 16.1.2(1) concerns L/Z(L). Its center equality
must be used before comparing this list with one about L/O₂(L).
These predicates and the two earlier-source inputs assert no classification
theorem. In particular the model lists contain genuine isomorphisms, and
their intersection remains a proof obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.1.34 on pp.29–30, A.3.8 on pp.45–46, and 16.1.2 on p.1170.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
open Subgroup Theory.GroupTheory ClassificationModels
universe u v

/-- The model clause of A.3.8(3), before intersection with (E2). -/
inductive SourceOrbitModel (S : Type u) [Group S] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL S 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | janko_one (iso : Nonempty (S ≃* Janko1.Model))
  | linear_odd (p : ℕ) (hp : p.Prime) (hlarge : 3 < p)
      (iso : ClassicalGroup.IsPSL S 2 p)

/-- Precisely the eight simple quotients in 16.1.2(1). -/
def NonsimpleSourceModel (S : Type u) [Group S] : Prop :=
  Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
    ClassicalGroup.IsPSL S 3 4 ∨ IsG2At S 4 ∨
    ∃ name : SporadicName,
      (name = .m12 ∨ name = .m22 ∨ name = .j2 ∨ name = .hs ∨ name = .ru) ∧
      Nonempty (S ≃* name.Carrier)

/-- The consumed model clause of A.3.8(3), with both standing hypotheses
from A.3.4. Its other conclusions are not needed for the list intersection. -/
def SourceA38Three (K : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK K H → pCore 2 H = ⊥ →
    ∀ B : Subgroup H, B.IsCComponent → ¬ B.Normal → SourceOrbitModel B

/-- Clause (1) of 16.1.2, under its actual standing centralizer hypotheses.
The source-theorem owner must discharge this earlier input. -/
def Source1612One (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  Hypothesis1611 K G → ∀ (t : G) (L : Subgroup G), orderOf t = 2 →
    IsCentralizerComponent t L → ¬ IsSimpleGroup L →
      center L = pCore 2 L ∧ NonsimpleSourceModel (L ⧸ center L)

variable {S : Type u} {R : Type v} [Group S] [Group R]

/-- Transport the entire source orbit list through an actual isomorphism. -/
theorem SourceOrbitModel.of_mulEquiv (h : SourceOrbitModel S) (e : R ≃* S) :
    SourceOrbitModel R := by
  cases h with
  | linear_even n hn iso => exact .linear_even n hn (iso.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun a => e.trans a)
  | janko_one iso => exact .janko_one (iso.map fun a => e.trans a)
  | linear_odd p hp hlarge iso => exact .linear_odd p hp hlarge (iso.of_mulEquiv e)

/-- Transport the nonsimple-cover list without changing its quotient convention. -/
theorem NonsimpleSourceModel.of_mulEquiv (h : NonsimpleSourceModel S) (e : R ≃* S) :
    NonsimpleSourceModel R := by
  rcases h with iso | iso | iso | ⟨name, hn, iso⟩
  · exact Or.inl (iso.map fun a => e.trans a)
  · exact Or.inr (Or.inl (iso.of_mulEquiv e))
  · exact Or.inr (Or.inr (Or.inl (iso.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr ⟨name, hn, iso.map fun a => e.trans a⟩))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
end
