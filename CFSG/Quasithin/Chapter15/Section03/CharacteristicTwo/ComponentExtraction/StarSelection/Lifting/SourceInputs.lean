module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.Quasithin.Rank

/-!
# Complete earlier source inputs for lifting the star component

These are universal theorem inputs, not assertions that A.3.8 or A.3.9 has
been proved. A.3.8 retains its separate ordinary-component theorem for a
merely quasithin K-group, its actual matrix/Suzuki/Janko models, and every
orbit, product and Sylow clause. A.3.9 retains both residual generation and
the component-layer equality after removing the generated group's odd core.

The source owner is `qt-a03-sqtk-structure`. The Chapter 15 application uses
A.3.9 to lift a prescribed component without assuming its preimage kernel
solvable, and A.3.8 to bound its orbit in the local overgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.8–9,
printed pp.45–46. Unitary parameters denote the fixed field (p.38, note 3).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.Lifting
universe u

/-- The complete ordinary-component model list of A.3.8(2). In particular
SU₃(8) is the special unitary group over a field of order 64. -/
inductive OrdinaryOrbitModel (X : Type u) [Group X] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL X 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | janko (iso : Nonempty (X ≃* Janko1.Model))
  | linear_odd (p e : ℕ) (hp : p.Prime) (hp3 : 3 < p) (he : 1 ≤ e ∧ e ≤ 2)
      (iso : ClassicalGroup.IsPSL X 2 (p ^ e))
  | unitary (F : Type) [Field F] [Finite F]
      (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
      (hcard : Nat.card F = 8 ^ 2) (hconj : ∀ x, J.conj x = x ^ 8)
      (iso : Nonempty (X ≃* J.specialSubgroup))

/-- A.3.8(3)'s stricter four-model list, with the source restriction p > 3. -/
inductive COrbitModel (X : Type u) [Group X] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL X 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | janko (iso : Nonempty (X ≃* Janko1.Model))
  | linear_prime (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
      (iso : ClassicalGroup.IsPSL X 2 p)

variable {X : Type u} [Group X]

/-- Actual conjugates under a specified subgroup of the ambient group. -/
def conjugatesUnder (L A : Subgroup X) : Set (Subgroup X) :=
  Set.range fun a : A => L.map (MulAut.conj (a : X)).toMonoidHom

/-- The intrinsic C-components of an overgroup, written as ambient subgroups. -/
def relativeComponents (A : Subgroup X) : Set (Subgroup X) :=
  {L | L ≤ A ∧ (L.subgroupOf A).IsCComponent}

/-- Multiplication identifies the join with the direct product of its specified
factors. The marked multiplication clause prevents an unrelated product label. -/
def InternalDirectPair (L D : Subgroup X) : Prop :=
  ∃ e : (L × D) ≃* ↥(L ⊔ D), ∀ (l : L) (d : D), (e (l, d) : X) = (l : X) * d

/-- Every clause of A.3.8(1)–(2), for the specified ordinary component. -/
def OrdinaryOrbitConclusion (L : Subgroup X) : Prop :=
  (Set.range fun x : X => L.map (MulAut.conj x).toMonoidHom).ncard = 2 ∧
    (∀ t : X, t ∉ normalizer (L : Set X) →
      sSup (Set.range fun x : X => L.map (MulAut.conj x).toMonoidHom) =
        L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ((sSup (Set.range fun x : X => L.map (MulAut.conj x).toMonoidHom) :
        Subgroup X) : Set X) =
          (L : Set X) * (L.map (MulAut.conj t).toMonoidHom : Set X)) ∧
    OrdinaryOrbitModel L

/-- The two alternatives in the final Sylow clause of A.3.8(3). Products are
literal products of subsets of X; all component assertions are relative. -/
def SylowOrbitConclusion (L : Subgroup X) (T : Sylow 2 X) : Prop :=
  (L.Normal ∧ conjugatesUnder L T = {L} ∧ relativeComponents (L ⊔ T) = {L} ∧
    ((L ⊔ T : Subgroup X) : Set X) = (L : Set X) * (T : Set X)) ∨
  (∃ t : T, (t : X) ∉ normalizer (L : Set X) ∧
    let D := L.map (MulAut.conj (t : X)).toMonoidHom
    conjugatesUnder L T = {L, D} ∧ relativeComponents (L ⊔ T) = {L, D} ∧
      ((L ⊔ T : Subgroup X) : Set X) = ((L ⊔ D : Subgroup X) : Set X) * (T : Set X))

/-- The full strongly quasithin C-component conclusion in A.3.8(3). -/
def COrbitConclusion (L : Subgroup X) : Prop :=
  (L.Normal ∨
    (Set.range fun x : X => L.map (MulAut.conj x).toMonoidHom).ncard = 2 ∧
      COrbitModel L ∧
      ∀ t : X, t ∉ normalizer (L : Set X) →
        sSup (Set.range fun x : X => L.map (MulAut.conj x).toMonoidHom) =
          L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
        InternalDirectPair L (L.map (MulAut.conj t).toMonoidHom)) ∧
    ∀ T : Sylow 2 X, SylowOrbitConclusion L T

/-- Complete universal A.3.8 input. Its proof remains with the earlier source
owner, including the merely-quasithin ordinary-component branch. -/
structure A38Input (K : GroupClass.{u}) : Prop where
  ordinary : ∀ (X : Type u) [Group X] [Finite X],
    IsQuasithin X → IsKGroup K X → ∀ L : Subgroup X,
      IsComponent X L → pCore 2 L = ⊥ → ¬ L.Normal → OrdinaryOrbitConclusion L
  cComponents : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK K X → pCore 2 X = ⊥ → ∀ L : Subgroup X,
      L.IsCComponent → COrbitConclusion L

/-- Both conclusions of A.3.9, under the full finite SQTK and trivial-two-core
hypotheses. The odd core is intrinsic to the generated C-component group. -/
def A39Input (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK K X → pCore 2 X = ⊥ →
    cComponentLayer X = solvableResidual X ∧
      componentLayer ((cComponentLayer X) ⧸ pPrimeCore 2 (cComponentLayer X)) = ⊤

/-- The source list implies the weaker Chapter 1 orbit-model list. -/
theorem COrbitModel.to_nonnormalCComponentModel (h : COrbitModel X) :
    Chapter1.Section02.NonnormalCComponentModel X := by
  cases h with
  | linear_even n hn h => exact .linear_even n hn h
  | suzuki m hm h => exact .suzuki m hm h
  | janko h => exact .janko h
  | linear_prime p hp hp3 h => exact .linear_prime p hp (hp.odd_of_ne_two (by omega)) h

/-- Extracting the bound does not replace the full A.3.8 input by a weaker
classification premise. -/
theorem A38Input.normal_or_index_two {K : GroupClass.{u}} (h : A38Input K)
    [Finite X] (hX : IsSQTK K X) (h2 : pCore 2 X = ⊥)
    {L : Subgroup X} (hL : L.IsCComponent) :
    L.Normal ∨ (normalizer (L : Set X)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel L := by
  rcases (h.cComponents X hX h2 L hL).1 with hn | ⟨hc, hm, _⟩
  · exact Or.inl hn
  · exact Or.inr ⟨(ncard_conjugates_eq_index_normalizer L).symm.trans hc,
      hm.to_nonnormalCComponentModel⟩

/-- The genuine SQTK property survives quotienting by the intrinsic two-core. -/
theorem sqtk_twoCore_quotient {K : GroupClass.{u}} [Finite X] (h : IsSQTK K X) :
    IsSQTK K (X ⧸ pCore 2 X) := by
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

/-- A.3.9(1) lifts from the two-core quotient through its solvable kernel. -/
theorem layer_eq_residual {K : GroupClass.{u}} (h39 : A39Input K)
    [Finite X] (hX : IsSQTK K X) : cComponentLayer X = solvableResidual X := by
  let _ := pCore_isNilpotent (p := 2) (G := X)
  exact cComponentLayer_eq_residual_of_quotient (pCore 2 X)
    (h39 _ (sqtk_twoCore_quotient hX) (pCore_quotient_pCore_eq_bot 2)).1

/-- The orbit bound in an arbitrary finite SQTK group, using the actual
solvable two-core quotient and the complete earlier source input. -/
theorem cComponent_normalizer_index_le_two {K : GroupClass.{u}} (h38 : A38Input K)
    [Finite X] (hX : IsSQTK K X) {L : Subgroup X} (hL : L.IsCComponent) :
    (normalizer (L : Set X)).index ≤ 2 := by
  rcases Chapter1.Section02.proposition_1_2_1_three_index_of_A_3_8
      (fun X _ _ hX h2 L hL => h38.normal_or_index_two hX h2 hL)
      (sqtk_twoCore_quotient hX) hL with hn | ⟨hi, _⟩
  · let _ := hn
    simp only [normalizer_eq_top, index_top]
    decide
  · exact hi.le

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.Lifting
