module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# Structural alternatives in the two-core quotient

`A36Conclusion` records the four alternatives and the common assertions after
the list in A.3.6. `Proposition121Four` retains the extra equality
`Z(L) = Φ(F*(L))` printed in 1.2.1(4d). These statements are deliberately
distinct: that equality does not occur in the displayed conclusion of A.3.6.

The proved reduction applies the universal A.3.6 statement to the actual
two-core quotient. It proves the first three alternatives in full and isolates
exactly the fourth-case center–Frattini issue. It does not assume that equality
as an earlier theorem, nor claim the complete Proposition 1.2.1(4).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.6, pp.43–45,
and Proposition 1.2.1(4), p.504.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open LocalModels
universe u

/-- The elementary natural-module alternative of A.3.6(3). -/
def A36Natural (K : Type u) [Group K] [Finite K] : Prop :=
  generalizedFitting K = fittingSubgroup K ∧
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ NaturalSL2Action K (generalizedFitting K) p

/-- The displayed A.3.6(4), including nilpotence, both prime restrictions and
the exact Sylow shapes. This does not include a center–Frattini assertion. -/
def A36Nilpotent (K : Type u) [Group K] [Finite K] : Prop :=
  generalizedFitting K = fittingSubgroup K ∧
    Group.IsNilpotent (generalizedFitting K) ∧
    IsSL (K ⧸ generalizedFitting K) 2 5 ∧
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (generalizedFitting K) →
      ((p % 5 = 1 ∨ p % 5 = 4) ∨ p = 5) ∧
      (OddExtraspecialThree p (pCore p K) ∨ HomocyclicTwo p (pCore p K))

/-- The common conclusions following the four cases of A.3.6. The derived
subgroup of the radical is expressed intrinsically in the ambient group. -/
def A36Common (K : Type u) [Group K] : Prop :=
  fittingSubgroup K = pPrimeCore 2 K ∧ IsQuasisimple (K ⧸ fittingSubgroup K) ∧
    ((fittingSubgroup K = generalizedFitting K ∧
        fittingSubgroup K ≤ solvableRadical K ∧
        (fittingSubgroup K).relIndex (solvableRadical K) = 2) ∨
      (fittingSubgroup K = center K ∧ fittingSubgroup K = solvableRadical K ∧
        (Nat.card (fittingSubgroup K) = 1 ∨ Nat.card (fittingSubgroup K) = 3))) ∧
    ⁅solvableRadical K, solvableRadical K⁆ = ⁅fittingSubgroup K, (⊤ : Subgroup K)⁆ ∧
    IsQuasisimple (K ⧸ ⁅solvableRadical K, solvableRadical K⁆)

/-- The four structural alternatives of the earlier proposition. -/
inductive A36Alternative {X : Type u} [Group X] [Finite X] (K : Subgroup X) : Prop
  | simple (component : IsComponent X K) (simple : IsSimpleGroup K)
      (model : TheoremCModel K)
  | cover (component : IsComponent X K)
      (center : Nonempty (Subgroup.center K ≃* Multiplicative (ZMod 3)))
      (model : ThreeCoverModel K)
  | natural (data : A36Natural K)
  | nilpotent (data : A36Nilpotent K)

/-- The complete earlier classification contract, not an assumption of the
stronger Chapter 1 conclusion. -/
def A36Conclusion {X : Type u} [Group X] [Finite X] (K : Subgroup X) : Prop :=
  A36Alternative K ∧ A36Common K

/-- The equality explicitly printed in Proposition 1.2.1(4d), with the
Frattini subgroup embedded back in its ambient component. -/
def CenterFrattini (K : Type u) [Group K] : Prop :=
  center K = (frattini (generalizedFitting K)).map (generalizedFitting K).subtype

/-- The exact four conclusions of 1.2.1(4). In (d), the source changes the
equivalent congruences `p ≡ ±1` to `p² ≡ 1` modulo five. -/
inductive Proposition121Four {X : Type u} [Group X] [Finite X] (K : Subgroup X) : Prop
  | simple (component : IsComponent X K) (simple : IsSimpleGroup K)
      (model : TheoremCModel K)
  | cover (component : IsComponent X K)
      (center : Nonempty (Subgroup.center K ≃* Multiplicative (ZMod 3)))
      (model : ChapterOneThreeCoverModel K)
  | natural (p : ℕ) (hp : p.Prime) (hlarge : 3 < p)
      (action : NaturalSL2Action K (generalizedFitting K) p)
  | nilpotent (nilpotent : Group.IsNilpotent (generalizedFitting K))
      (center_frattini : CenterFrattini K)
      (quotient : IsSL (K ⧸ generalizedFitting K) 2 5)
      (cores : ∀ p : ℕ, p.Prime → p ∣ Nat.card (generalizedFitting K) →
        (p ^ 2 % 5 = 1 ∨ p = 5) ∧
        (OddExtraspecialThree p (pCore p K) ∨ HomocyclicTwo p (pCore p K)))

private theorem squared_congruence {p : ℕ}
    (hp : (p % 5 = 1 ∨ p % 5 = 4) ∨ p = 5) : p ^ 2 % 5 = 1 ∨ p = 5 := by
  rcases hp with (h | h) | h
  · left; simp [Nat.pow_mod, h]
  · left; simp [Nat.pow_mod, h]
  · exact Or.inr h

/-- The actual A.3.6 conclusion for the image of a C-component in `G/O₂(G)`. -/
theorem proposition_1_2_1_four_earlier_conclusion {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X,
      K.IsCComponent → A36Conclusion K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {K : Subgroup G} (hK : K.IsCComponent) :
    A36Conclusion (K.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  exact hA36 _ hQ (pCore_quotient_pCore_eq_bot 2) _ (hK.map_quotient _)

/-- All structural cases are discharged except exactly the additional printed
center–Frattini assertion. The second disjunct is an unresolved source case,
not a fifth classification alternative. -/
theorem proposition_1_2_1_four_reduction {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X,
      K.IsCComponent → A36Conclusion K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {K : Subgroup G} (hK : K.IsCComponent) :
    Proposition121Four (K.map (QuotientGroup.mk' (pCore 2 G))) ∨
      (A36Nilpotent (K.map (QuotientGroup.mk' (pCore 2 G))) ∧
        A36Common (K.map (QuotientGroup.mk' (pCore 2 G))) ∧
        ¬ CenterFrattini (K.map (QuotientGroup.mk' (pCore 2 G)))) := by
  classical
  obtain ⟨halt, hcommon⟩ := proposition_1_2_1_four_earlier_conclusion hA36 hQ hK
  cases halt with
  | simple hc hs hm => exact Or.inl (.simple hc hs hm)
  | cover hc hz hm => exact Or.inl (.cover hc hz hm.toChapterOne)
  | natural h =>
      obtain ⟨p, hp, hlarge, haction⟩ := h.2
      exact Or.inl (.natural p hp hlarge haction)
  | nilpotent h =>
      by_cases hz : CenterFrattini (K.map (QuotientGroup.mk' (pCore 2 G)))
      · exact Or.inl (.nilpotent h.2.1 hz h.2.2.1 (fun p hp hd =>
          ⟨squared_congruence (h.2.2.2 p hp hd).1, (h.2.2.2 p hp hd).2⟩))
      · exact Or.inr ⟨h, hcommon, hz⟩

end CFSG.Quasithin.Chapter1.Section02
