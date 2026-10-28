module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Census
public import Theory.GroupAction.CoprimeCentralizerLift

/-!
# Direct containment of the local planes in the cubic blocks

The action of an order-three group on the central binary group `V` is
coprime. Consequently `D` fixing `A/V` gives the stronger conclusion
`A ≤ C_P(D)V`. This supplies the plane-to-block reduction without assuming
any global fusion conclusion or a normalizer moving `V`.

The construction of the cubics and their fixed quotient lines is a separate
obligation. Source: Aschbacher–Smith, 15.3.54 and 15.3.61(2), pp.1146,1150.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G] [Finite G]

/-- Coprime lifting replaces the intermediate fusion reductions by containment. -/
theorem le_fusionBlock_of_fixed_quotient (A P V D : Subgroup G)
    (hAP : A ≤ P) (hVP : V ≤ P)
    [(V.subgroupOf P).Normal] [IsMulCommutative (V.subgroupOf P)]
    (hDP : D ≤ normalizer (P : Set G))
    (hDV : D ≤ normalizer (V : Set G))
    (hD : Nat.card D = 3) (hV : Nat.card V = 16)
    (hfixed : ∀ x ∈ A, ∀ d ∈ D, MulAut.conj d x / x ∈ V) :
    A ≤ fusionBlock P V D := by
  intro x hx
  exact mem_centralizer_sup_of_coprime_fixed_coset P V D hVP hDP hDV
    (by rw [hD, hV]; decide) x (hAP hx) (hfixed x hx)

/-- The exact reduction required by the residual-fusion assembly, for the
actual fixed lift and the corrected local planes. -/
theorem localPlane_reduction_of_fixed_quotient
    (Z ZS V : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (g : G) (a : centralizerH Z)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (i : Fin 2) (D : Subgroup G)
    (hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g)
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    [IsMulCommutative (V.subgroupOf (pairP Z ZS g))]
    (hDP : D ≤ normalizer (pairP Z ZS g : Set G))
    (hDV : D ≤ normalizer (V : Set G))
    (hD : Nat.card D = 3) (hV : Nat.card V = 16)
    (hfixed : ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
      ∀ d ∈ D, MulAut.conj d x / x ∈ V) :
    ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i, orderOf x = 2 →
      ∃ y, (y ∈ closureU Z ZS ∨ y ∈ fusionBlock (pairP Z ZS g) V D) ∧
        ConjugateBy (pairI Z ZS g) x y := by
  have hle := le_fusionBlock_of_fixed_quotient _ _ V D
    ((localPlane_le _ e i).trans hLP) (le_sup_right.trans hLP)
    hDP hDV hD hV hfixed
  intro x hx _
  exact ⟨x, Or.inr (hle hx), ConjugateBy.refl _ _⟩

omit [Finite G] in
/-- Once `P` lies in the actual residual Sylow group, so does every block. -/
theorem fusionBlock_le_residualSylow (T Z ZS V D : Subgroup G) (g : G)
    (hVP : V ≤ pairP Z ZS g)
    (hPT : pairP Z ZS g ≤ residualSylow T Z) :
    fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z :=
  sup_le (inf_le_left.trans hPT) (hVP.trans hPT)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
