module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup
public import Theory.GroupTheory.InvertingConjugates
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.PPrimeCore

/-!
# The odd-core reduction for the A₅ centralizer

The marked binary module constructs three Lᵥ-conjugates of z whose product
is v. Once the earlier 1.1.5 input says that z inverts O(Gᵥ), normality makes
each conjugate invert it. Their product is central in Gᵥ, so the odd core is
trivial. Thus the product calculation discharges the odd-core step without
assuming its conclusion or a characteristic-two certificate.

The source-specific configuration, applicability of 1.1.5, and elimination
of all component alternatives still have to be supplied before asserting
F*(Gᵥ) = O₂(Gᵥ). This module does not yet assert Lemma 13.6.6.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
13.6.6, printed pp.926–928.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The odd-core step, using an actual module marking and precisely the
inversion conclusion of the earlier 1.1.5. The three residual conjugates
and their central product are constructed, not assumed. -/
public theorem oddCore_eq_bot_of_marked_module (s : Marking L V)
    (hinvert : ∀ x : Gv (markedV s), x ∈ pPrimeCore 2 (Gv (markedV s)) →
      MulAut.conj (markedZ s) (x : G) = (x : G)⁻¹) :
    pPrimeCore 2 (Gv (markedV s)) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hproduct⟩ := exists_residual_triple s
  let z' : Gv (markedV s) := ⟨markedZ s, markedZ_mem_Gv s⟩
  let c' : Gv (markedV s) := ⟨c, Lv_le_Gv L (markedV s) hc⟩
  apply eq_bot_of_conjugate_inverters (pPrimeCore 2 (Gv (markedV s)))
    pPrimeCore_coprime_card z' c' (c' ^ 2)
  · intro x hx
    exact Subtype.ext (hinvert x hx)
  · have he : z' * MulAut.conj c' z' * MulAut.conj (c' ^ 2) z' =
        centralElement (markedV s) := Subtype.ext hproduct
    rw [he]
    have hz : centralElement (markedV s) ∈ center (Gv (markedV s)) :=
      vLine_le_center _ (mem_zpowers _)
    exact mem_centralizer_iff.mpr fun x _ => mem_center_iff.mp hz x

/-- After the odd core has been eliminated, failure of characteristic two
produces an actual subnormal quasisimple subgroup of Gᵥ. This is the
component entering the remaining source case analysis. -/
public theorem exists_component_of_not_characteristic_two (s : Marking L V)
    (hinvert : ∀ x : Gv (markedV s), x ∈ pPrimeCore 2 (Gv (markedV s)) →
      MulAut.conj (markedZ s) (x : G) = (x : G)⁻¹)
    (hnot : Theory.GroupTheory.generalizedFitting (Gv (markedV s)) ≠
      pCore 2 (Gv (markedV s))) :
    ∃ K : Subgroup (Gv (markedV s)),
      Theory.GroupTheory.IsComponent (Gv (markedV s)) K := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hn
  have hE : Theory.GroupTheory.componentLayer (Gv (markedV s)) = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    exact (hn ⟨K, hK⟩).elim
  apply hnot
  rw [Theory.GroupTheory.generalizedFitting, hE, sup_bot_eq]
  exact Fitting_eq_pcore _ 2 (oddCore_eq_bot_of_marked_module s hinvert)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
