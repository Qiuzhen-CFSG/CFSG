module

public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.Quasisimple
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.CyclicThree

/-!
# Structure of an internal module with a Sylow supplement

Let `V` be a normal elementary abelian two-subgroup of a finite group `G`,
and let `q : G → H` be onto with kernel `C_G(V)` and `O₂(H) = 1`. Suppose
`G = LT`, where `T` is Sylow, `[V,L] ≠ 1`, and either `L` is a C-component
with quasisimple `L/O₂(L)`, or `L/O₂(L)` is cyclic of order three.
Then the centralizer has a normal Sylow two-subgroup with ambient image
`O₂(G) = T ∩ C_G(V)`, and `q(L) = F*(H)` is quasisimple or has order three.
Every normal subgroup of `H` containing a nontrivial two-subgroup has the
same generalized Fitting subgroup, through its actual inclusion into `H`.

The two structural branches provide the centralizer's Sylow subgroup and
identify the image of `L`. The normal-subgroup deduction then uses component
dichotomy and self-centralization of the generalized Fitting subgroup.
No normality of `L` is assumed, and the product hypothesis is setwise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.2.10(2), printed p.77, under Hypothesis B.2.1, printed p.74
(combined manuscript of 1 March 2004).
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The centralizer and actual quotient image under the two source alternatives.
All Sylow and generalized-Fitting conclusions are derived from the factorization. -/
theorem internalModule_residual_structure
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G) (L : Subgroup G)
    (hL : (L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    pCore 2 G = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    (∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal ∧
      (P : Subgroup (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = pCore 2 G) ∧
    L.map q = generalizedFitting H ∧
    (IsQuasisimple (L.map q) ∨ Nat.card (L.map q) = 3) := by
  have hstructure :
      (∃ P : Sylow 2 (centralizer (V : Set G)),
        (P : Subgroup (centralizer (V : Set G))).Normal) ∧
      L.map q = generalizedFitting H ∧
      (IsQuasisimple (L.map q) ∨ Nat.card (L.map q) = 3) := by
    rcases hL with ⟨hcomponent, hquasi⟩ | hthree
    · obtain ⟨hP, hF, hshape⟩ := internalModule_quasisimple_structure
        V q hq hker hcore T L hcomponent hquasi hcomm hprod
      exact ⟨hP, hF, Or.inl hshape⟩
    · obtain ⟨hP, hF, hshape⟩ := cyclic_three_image_structure
        V L q hq hker hcore T hthree hcomm hprod
      exact ⟨hP, hF, Or.inr hshape⟩
  obtain ⟨hcoreG, hP⟩ := normalSylow_structure_of_coreFree_image
    q hq hcore (centralizer (V : Set G)) hker T hstructure.1
  exact ⟨hcoreG, hP, hstructure.2⟩

/-- Under the source factorization, every normal subgroup containing a
nontrivial two-subgroup has generalized Fitting image exactly `q(L)`.
In particular this applies to a nontrivial elementary abelian two-subgroup. -/
theorem internalModule_normal_generalizedFitting
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G) (L : Subgroup G)
    (hL : (L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g)
    (N A : Subgroup H) [N.Normal] (hA : IsPGroup 2 A)
    (hne : A ≠ ⊥) (hAN : A ≤ N) :
    (generalizedFitting N).map N.subtype = L.map q := by
  obtain ⟨_, _, hF, hshape⟩ :=
    internalModule_residual_structure V q hq hker hcore T L hL hcomm hprod
  exact (generalizedFitting_normal_eq_of_quasisimple_or_three hcore
    (hF ▸ hshape) N A hA hne hAN).trans hF.symm

end Theory.GroupTheory
