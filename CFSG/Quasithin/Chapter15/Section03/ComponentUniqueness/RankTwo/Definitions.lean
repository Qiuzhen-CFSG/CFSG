module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Uniqueness
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Quotients and the conclusion of 15.3.35

These definitions retain the centralizer denominator in `I⁺`, the Frattini
preimage in the rank-two shadow, and all five clauses of 15.3.35. They make
no classification assertion. In particular, `O_{2,Φ}` is not `O₂`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.35--41, printed pp.1135--1138. The convention for `O_{2,Φ}` is
specified in the footnote on printed p.491.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Case (2) of Hypothesis 15.3.10, with its uniqueness premise. -/
def CaseTwo (M Y S V₁ Yplus : Subgroup G) : Prop :=
  Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M ∧
    Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G))

/-- The preimage of the Frattini subgroup of `G/O₂(G)`. -/
def twoFrattiniCore (G : Type*) [Group G] : Subgroup G :=
  (frattini (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))

instance twoFrattiniCore_normal : (twoFrattiniCore G).Normal := by
  unfold twoFrattiniCore
  infer_instance

/-- The rank-two quotient in 15.3.36 and 15.3.41. -/
def RankTwoShadow (Yplus S : Subgroup G) : Prop :=
  Nonempty (((Yplus ⊔ S : Subgroup G) ⧸ twoFrattiniCore (Yplus ⊔ S : Subgroup G)) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

/-- The complete conclusion of 15.3.35, with the residual formed inside `M ∩ I`. -/
def Conclusion (M Y S V₁ V₂ Yplus I : Subgroup G) : Prop :=
  CaseTwo M Y S V₁ Yplus ∧
    SymmetricThreeShadow Yplus S ∧
    Yplus = (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ∧
    Yplus < Y ∧
    (Yplus ⊔ S : Subgroup G).pCoreIn 2 = S ⊓ centralizer (V₂ : Set G)

/-- `I⁺ = I/C_I(L ∩ I)`, hence `I/C_I(L)` when `L ≤ I`.
Normality is required only inside `I`. -/
abbrev ComponentQuotient (I L : Subgroup G) := CentralizerQuotient (L.subgroupOf I)

/-- The image of `X ∩ I` under the component-action quotient. -/
def componentImage (I L X : Subgroup G) [(L.subgroupOf I).Normal] :
    Subgroup (ComponentQuotient I L) :=
  (X.subgroupOf I).map (centralizerQuotientMap (L.subgroupOf I))

/-- Identify the denominator with the relative centralizer in the source.
The containment hypothesis prevents silently replacing `L` by `L ∩ I`. -/
theorem component_kernel_eq (I L : Subgroup G) [(L.subgroupOf I).Normal]
    (hLI : L ≤ I) :
    (centralizerQuotientMap (L.subgroupOf I)).ker =
      (centralizer (L : Set G)).subgroupOf I := by
  rw [centralizerQuotientMap, QuotientGroup.ker_mk']
  ext x
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (hx (⟨y, hLI hy⟩ : I) hy)
  · intro hx y hy
    exact Subtype.ext (hx y hy)

/-- The subgroup and action conclusions of 15.3.41(2), for use by the
subsequent simple-group analysis. This is a conclusion interface: its
fields must be proved in the actual component quotient. No theorem here
asserts that this configuration exists. -/
structure LocalConfiguration (L M Yplus S : Subgroup G) : Prop where
  twoLocal : IsTwoLocal M
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  sylow_le : S ≤ M
  yplus_le : Yplus ≤ M ⊓ L
  yplus_normal : (Yplus.subgroupOf (M ⊓ L)).Normal
  shadow : RankTwoShadow Yplus S
  characteristicTwo : generalizedFitting M = pCore 2 M
  maximal : ∀ J : Subgroup G, M ≤ J → generalizedFitting J = pCore 2 J → J = M

end CFSG.Quasithin.Chapter15.Section03.RankTwo
