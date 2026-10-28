module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.AbelianBySymmetricThree
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The local centralizer interfaces for §7.7

This file records the group-theoretic deductions used in the centralizer part
of the binary natural-plus-dual argument.  The representation calculation and
the component sieve are deliberately inputs to these lemmas: they are proved
from the actual `L⁰`, `T₀`, and model data by the §7.7 assembly.

The first lemma is Proposition 7.7.2 after its characteristic-two input has
been established.  The second is the quotient calculation behind Lemma
7.7.4.  The final lemmas are the Frattini and self-centralizing-core steps in
Lemma 7.7.6; in particular, the equality with `O₂` is obtained from a genuine
self-centralizing-core hypothesis, rather than from a conclusion-bearing
record.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §§7.7.2,
7.7.4 and 7.7.6, printed pp. 704--706.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter7.Section06To07

variable {G : Type*} [Group G]

/-- Proposition 7.7.2 once the source has proved characteristic two for the
centralizer in question.  The hypothesis is exactly the self-centralizing
`O₂` condition; no stronger generalized-Fitting equality is assumed. -/
public theorem proposition_7_7_2_of_characteristicTwo
    [Finite G]
    (C : Subgroup G) (hC : HasCharacteristicTwo C) :
    generalizedFitting C = pCore 2 C := by
  exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2 hC

/-- The same conclusion in the notation used for a centralizer.  This is the
form consumed after the natural/dual module argument has supplied `hC`. -/
public theorem proposition_7_7_2_centralizer
    [Finite G]
    (X : Set G) (hC : HasCharacteristicTwo (centralizer X)) :
    generalizedFitting (centralizer X) = pCore 2 (centralizer X) := by
  exact proposition_7_7_2_of_characteristicTwo _ hC

/-- In an `S₃` quotient, an odd subgroup centralizing an involution lies in
the odd kernel.  This is the precise quotient step used in the index bound of
Lemma 7.7.4; the source supplies the quotient and identifies its kernel with
`O²(C_M(V⁺))`. -/
public theorem lemma_7_7_4_odd_centralizer_le_kernel
    (A Y : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (e : G ⧸ A ≃* Equiv.Perm (Fin 3))
    (hYodd : Odd (Nat.card Y)) (t : G) (ht : orderOf t = 2) :
    Y ⊓ centralizer ({t} : Set G) ≤ A := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' A)
  have hker : f.ker = A := by
    ext x
    change e (QuotientGroup.mk' A x) = 1 ↔ x ∈ A
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  rw [← hker]
  exact Subgroup.AbelianBySymmetricThree.odd_centralizer_le_kernel f
    (by simpa [hker] using hAodd) Y hYodd t ht

/-- The corresponding fixed-point index divides three times the fixed-point
index on the odd kernel.  In the source application the latter index is one,
so this specializes to the displayed `≤ 3` bound. -/
public theorem lemma_7_7_4_centralizer_index_dvd
    (A Y : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (e : G ⧸ A ≃* Equiv.Perm (Fin 3))
    (hYodd : Odd (Nat.card Y)) (t : G) (ht : orderOf t = 2) :
    (centralizer ({t} : Set G)).relIndex Y ∣
      3 * (centralizer ({t} : Set G)).relIndex A := by
  exact Subgroup.AbelianBySymmetricThree.centralizer_relIndex_dvd_of_s3_quotient
    A Y hAodd e hYodd t ht

/-- The displayed `≤ 3` form of Lemma 7.7.4.  The source's model identifies
the odd kernel centralizes the involution, which is the explicit `hcentral`
hypothesis here. -/
public theorem lemma_7_7_4_centralizer_index_le_three
    (A Y : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (e : G ⧸ A ≃* Equiv.Perm (Fin 3))
    (hYodd : Odd (Nat.card Y)) (t : G) (ht : orderOf t = 2)
    (hcentral : A ≤ centralizer ({t} : Set G)) :
    (centralizer ({t} : Set G)).relIndex Y ≤ 3 := by
  have hd := lemma_7_7_4_centralizer_index_dvd A Y hAodd e hYodd t ht
  have hone : (centralizer ({t} : Set G)).relIndex A = 1 :=
    relIndex_eq_one.mpr hcentral
  rw [hone, Nat.mul_one] at hd
  exact Nat.le_of_dvd (by decide) hd

/-- The Sylow conclusion in Lemma 7.7.6, proved from the usual maximality
characterization rather than by projecting a pre-existing `IsSylowIn` record. -/
public theorem lemma_7_7_6_sylow
    [Finite G]
    {H T : Subgroup G}
    (hTgroup : IsPGroup 2 T) (hTH : T ≤ H)
    (hTmax : ∀ U : Subgroup G, IsPGroup 2 U → T ≤ U → U ≤ H → U = T) :
    Chapter1.IsSylowIn 2 T H := by
  exact Chapter1.isSylowIn_iff.mpr ⟨hTgroup, hTH, hTmax⟩

/-- Frattini factorization by the elementary Thompson subgroup.  If `T` is
the chosen Sylow subgroup and its elementary Thompson subgroup has normalizer
inside `U`, then `J(G) U = G`.  The source applies this with
`U = L⁰ T₀`; the normalizer containment is the separate 3.2.10.8 input. -/
public theorem lemma_7_7_6_thompson_factorization
    [Finite G]
    (S : Sylow 2 G) (U : Subgroup G)
    (hN : normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) ≤ U) :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) ⊔ U = ⊤ := by
  have hF := Stellmacher.elementaryAbelianMaxJ_frattini S
  have hle : normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔
      Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ U ⊔
        Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) :=
    sup_le (hN.trans le_sup_left) le_sup_right
  have htop : (⊤ : Subgroup G) ≤ U ⊔
      Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) := by
    calc
      (⊤ : Subgroup G) =
          normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔
            Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) := hF.symm
      _ ≤ U ⊔ Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup G) := hle
  exact le_antisymm le_top (by simpa [sup_comm] using htop)

/-- The third conclusion of Lemma 7.7.6 from the characteristic-two statement
proved by the preceding local analysis. -/
public theorem lemma_7_7_6_fitting
    [Finite G]
    (H : Subgroup G) (hH : HasCharacteristicTwo H) :
    generalizedFitting H = pCore 2 H := by
  exact proposition_7_7_2_of_characteristicTwo H hH

end CFSG.Quasithin.Chapter7.Section06To07

end
