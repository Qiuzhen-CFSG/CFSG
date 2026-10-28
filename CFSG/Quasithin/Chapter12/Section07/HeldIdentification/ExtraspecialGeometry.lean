module

public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.Defs
public import Theory.GroupTheory.FullStabilizerCore
public import Theory.ElementaryAbelian.Basic
public import Theory.Representation.PSL3Two.NaturalDualCoreObstruction
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Core and module reductions for the Held extraspecial configuration

The invariant-subgroup alternatives for O₂(C_G(z)) leave the central line,
two proper elementary subgroups, or P. Characteristic two excludes the line;
the full z-stabilizer action on either elementary subgroup excludes that
candidate. A scalar moving z in its four-group then gives the actual
ambient conjugate required by Aschbacher's recognition theorem.

The module lemmas below use conjugation on the literal P/Z(P) inside
C_G(z). They exclude either marked Fano permutation core once that same
module has the split natural-plus-dual action. The construction of P,Y,
their actions and marked local comparisons, the overgroup classification,
and the extension isomorphism remain necessary. No centralizer or Held
identification is claimed by these conditional reductions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Theorem 12.7.7, printed pp.841–842 (PDF pp.858–859).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07.HeldIdentification.ExtraspecialGeometry
variable {G : Type*} [Group G]

/-- Source core reduction: eliminate the central line and both natural
summands using the actual action, leaving the whole extraspecial group.
The invariant-subgroup classification and full stabilizer calculations
are still explicit inputs; the final source owner must construct them. -/
theorem core_eq_of_candidates (P Y : Subgroup G) (A : Fin 2 → Subgroup G)
    (z : G) (hP : IsPGroup 2 P) (hPY : P ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G))
    (hYC : Y ≤ centralizer ({z} : Set G))
    (hZ : ¬ P ≤ closure ({z} : Set G))
    (hproper : ∀ i, A i < P) (hz : ∀ i, z ∈ A i)
    (hYA : ∀ i, Y ≤ normalizer (A i : Set G))
    (hC : centralizer ({z} : Set G) ⊓
      centralizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
        (centralizer ({z} : Set G)).pCoreIn 2)
    (hlift : ∀ i, ∀ a : MulAut (A i), a ⟨z, hz i⟩ = ⟨z, hz i⟩ →
      ∃ y : Y, (A i).normalizerMonoidHom ⟨y, hYA i y.property⟩ = a)
    (hcases : (centralizer ({z} : Set G)).pCoreIn 2 = closure ({z} : Set G) ∨
      (∃ i, (centralizer ({z} : Set G)).pCoreIn 2 = A i) ∨
      (centralizer ({z} : Set G)).pCoreIn 2 = P) :
    (centralizer ({z} : Set G)).pCoreIn 2 = P := by
  rcases hcases with he | ⟨i, he⟩ | he
  · have hle : centralizer ({z} : Set G) ≤ closure ({z} : Set G) := by
      simpa only [he, centralizer_closure, inf_idem] using hC
    exact False.elim (hZ (hPY.trans (hYC.trans hle)))
  · exact False.elim (core_ne_of_full_stabilizer P Y (A i) z (hz i) hP hPY hYP
      hYC (hproper i).le (hproper i).not_ge (hYA i) hC (hlift i) he)
  · exact he

/-- A scalar moving z in its four-group supplies the literal conjugate
needed for Asc94 44.4 once the core has been identified. -/
theorem scalar_conjugate_in_core (P V₁ : Subgroup G) [IsElementaryAbelian 2 V₁]
    (z x : G) (hz : z ∈ V₁) (hne : z ≠ 1)
    (hx : x ∈ normalizer (V₁ : Set G)) (hmove : MulAut.conj x z ≠ z)
    (hV : V₁ ≤ P) (hcore : (centralizer ({z} : Set G)).pCoreIn 2 = P) :
    orderOf z = 2 ∧ MulAut.conj x z ∈ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      MulAut.conj x z ≠ z := by
  refine ⟨orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hne, ?_, hmove⟩
  rw [hcore]
  exact hV ((hx z).mp hz)

/-- Conjugation by the actual element centralizer on a normal subgroup's
central quotient. In the source application P is the core just identified. -/
noncomputable def quotientRepresentation (z : G)
    (P : Subgroup (centralizer ({z} : Set G))) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)] :
    Representation (ZMod 2) (centralizer ({z} : Set G)) (Additive (P ⧸ center P)) :=
  Representation.elementaryRepresentation (normalQuotientAction P (center P))

/-- The action uses the original quotient map and conjugation convention. -/
theorem quotientRepresentation_apply (z : G)
    (P : Subgroup (centralizer ({z} : Set G))) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (g : centralizer ({z} : Set G)) (p : P) :
    quotientRepresentation z P g (Additive.ofMul (QuotientGroup.mk' (center P) p)) =
      Additive.ofMul (QuotientGroup.mk' (center P) (MulAut.conjNormal g p)) := by
  change Additive.ofMul (normalQuotientAction P (center P) g
    (QuotientGroup.mk' (center P) p)) = _
  rw [normalQuotientAction_apply_mk]

open Representation BinaryLinearThree
open BinaryLinearThree.FanoDecomposition

/-- The point-marked A₇ module cannot extend the actual split action on P/Z(P).
The local extension supplies i; the orthogonal-overgroup analysis must still
supply j, its marking, and the genuine deleted-module equivalence ecore. -/
theorem exclude_point_core_centralizer_action (z : G)
    (P : Subgroup (centralizer ({z} : Set G))) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (i : BinaryLinearThree.Group →* centralizer ({z} : Set G))
    (j : centralizer ({z} : Set G) →* Equiv.Perm Point)
    (hmark : ∀ g, j (i g) = pointPerm g)
    (ecore : Representation.Equiv (quotientRepresentation z P)
      ((BinaryPermutation.coreRepresentation Point).comp j))
    (esplit : Representation.Equiv ((quotientRepresentation z P).comp i) (W.prod W.dual)) :
    False :=
  NaturalDualCoreObstruction.no_marked_point_core_extension
    (quotientRepresentation z P) i j hmark ecore esplit

/-- The line-marked seven-point action gives the same contradiction, on the
same literal central quotient. Neither marking may be replaced by an order. -/
theorem exclude_line_core_centralizer_action (z : G)
    (P : Subgroup (centralizer ({z} : Set G))) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (i : BinaryLinearThree.Group →* centralizer ({z} : Set G))
    (j : centralizer ({z} : Set G) →* Equiv.Perm Line)
    (hmark : ∀ g, j (i g) = linePerm g)
    (ecore : Representation.Equiv (quotientRepresentation z P)
      ((BinaryPermutation.coreRepresentation Line).comp j))
    (esplit : Representation.Equiv ((quotientRepresentation z P).comp i) (W.prod W.dual)) :
    False :=
  NaturalDualCoreObstruction.no_marked_line_core_extension
    (quotientRepresentation z P) i j hmark ecore esplit

end CFSG.Quasithin.Chapter12.Section07.HeldIdentification.ExtraspecialGeometry
