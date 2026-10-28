module

public import CFSG.Quasithin.ChapterA.Section04.Defs
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# The centralizer of the section X/O₂(X)

An element of C_M(X/O₂(X)) lies in M, normalizes X, and acts trivially
modulo the embedded two-core. The commutator membership criterion gives
closure under multiplication and inversion; characteristicness of O₂(X)
ensures that conjugation preserves the layer. The equivalent commutator
preimage description gives normality inside N_M(X).

The two-core lies in every Sylow two-subgroup of this centralizer, so each
such Sylow subgroup is an X-signalizer. Source: Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.4.2(3)–(5), printed p. 57.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G]

def twoSectionCentralizer (X M : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ M ∧ g ∈ normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅g, x⁆ ∈ X.pCoreIn 2}
  one_mem' := ⟨M.one_mem, (normalizer (X : Set G)).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haM, haN, ha⟩ ⟨hbM, hbN, hb⟩
    refine ⟨M.mul_mem haM hbM, (normalizer (X : Set G)).mul_mem haN hbN, ?_⟩
    intro x hx
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact (X.pCoreIn 2).mul_mem
      ((mem_normalizer_iff.mp
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X) haN) _).mp (hb x hx))
      (ha x hx)
  inv_mem' := by
    rintro g ⟨hgM, hgN, hg⟩
    refine ⟨M.inv_mem hgM, (normalizer (X : Set G)).inv_mem hgN, ?_⟩
    intro x hx
    rw [commutatorElement_inv_left]
    have hc : ⁅x, g⁆ ∈ X.pCoreIn 2 := by
      rw [← commutatorElement_inv]
      exact (X.pCoreIn 2).inv_mem (hg x hx)
    have hn := normalizer_le_normalizer_characteristic_image X (pCore 2 X)
      ((normalizer (X : Set G)).inv_mem hgN)
    simpa only [inv_inv, pCoreIn] using (mem_normalizer_iff.mp hn _).mp hc

theorem mem_twoSectionCentralizer (X M : Subgroup G) (g : G) :
    g ∈ twoSectionCentralizer X M ↔
      g ∈ M ∧ g ∈ normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅g, x⁆ ∈ X.pCoreIn 2 := Iff.rfl

theorem le_twoSectionCentralizer_iff (X M R : Subgroup G) :
    R ≤ twoSectionCentralizer X M ↔ R ≤ M ∧ R ≤ normalizer (X : Set G) ∧ ⁅X,R⁆ ≤ X.pCoreIn 2 := by
  rw [commutator_comm X R, commutator_le]
  constructor
  · intro h
    exact ⟨fun _ hr => (h hr).1, fun _ hr => (h hr).2.1, fun r hr => (h hr).2.2⟩
  · rintro ⟨hM, hN, hc⟩ r hr
    exact ⟨hM hr, hN hr, hc r hr⟩

theorem twoSectionCentralizer_le (X M : Subgroup G) : twoSectionCentralizer X M ≤ M :=
  fun _ h => h.1

theorem twoSectionCentralizer_le_normalizer (X M : Subgroup G) :
    twoSectionCentralizer X M ≤ normalizer (X : Set G) := fun _ h => h.2.1

theorem pCoreIn_le_twoSectionCentralizer (X M : Subgroup G) (hXM : X ≤ M) :
    X.pCoreIn 2 ≤ twoSectionCentralizer X M := by
  apply (le_twoSectionCentralizer_iff X M _).mpr
  refine ⟨(pCoreIn_le 2 X).trans hXM, (pCoreIn_le 2 X).trans le_normalizer, ?_⟩
  apply le_normalizer_iff_commutator_le_right.mp
  exact le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))

theorem twoSectionCentralizer_eq_commutatorPreimage (X M : Subgroup G) :
    twoSectionCentralizer X M = commutatorPreimage (M ⊓ normalizer (X : Set G)) X (X.pCoreIn 2) := by
  have hn : M ⊓ normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2) :=
    inf_le_right.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  apply le_antisymm
  · apply le_commutatorPreimage
    · exact le_inf (twoSectionCentralizer_le X M) (twoSectionCentralizer_le_normalizer X M)
    · rw [commutator_comm]
      exact ((le_twoSectionCentralizer_iff X M _).mp le_rfl).2.2
  · apply (le_twoSectionCentralizer_iff X M _).mpr
    have hc := commutatorPreimage_le (M ⊓ normalizer (X : Set G)) X (X.pCoreIn 2)
    refine ⟨hc.trans inf_le_left, hc.trans inf_le_right, ?_⟩
    rw [commutator_comm]
    exact commutator_commutatorPreimage_le _ _ _ hn
theorem normalizer_twoSectionCentralizer (X M : Subgroup G) :
    M ⊓ normalizer (X : Set G) ≤ normalizer (twoSectionCentralizer X M : Set G) := by
  rw [twoSectionCentralizer_eq_commutatorPreimage]
  have hn : M ⊓ normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  exact commutatorPreimage_normalized _ _ _ _ hn le_normalizer inf_le_right hn

theorem signalizer_of_le_twoSectionCentralizer (X M R : Subgroup G)
    (hR : IsPGroup 2 R) (hRC : R ≤ twoSectionCentralizer X M)
    (hcore : X.pCoreIn 2 ≤ R) : IsTwoSignalizer X M R := by
  have h := (le_twoSectionCentralizer_iff X M R).mp hRC
  exact (isTwoSignalizer_iff_commutator_le X M R h.1 hR).mpr (h.2.2.trans hcore)

theorem pCoreIn_le_sylow_twoSectionCentralizer (X M : Subgroup G) (hXM : X ≤ M)
    (S : Sylow 2 (twoSectionCentralizer X M)) :
    X.pCoreIn 2 ≤ (S : Subgroup (twoSectionCentralizer X M)).map
      (twoSectionCentralizer X M).subtype := by
  apply (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
    (pCoreIn_le_twoSectionCentralizer X M hXM) ?_).trans
    (pCoreIn_le_sylow _ S)
  exact (twoSectionCentralizer_le_normalizer X M).trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))

theorem sylow_twoSectionCentralizer_isSignalizer (X M : Subgroup G) (hXM : X ≤ M)
    (S : Sylow 2 (twoSectionCentralizer X M)) :
    IsTwoSignalizer X M ((S : Subgroup (twoSectionCentralizer X M)).map
      (twoSectionCentralizer X M).subtype) :=
  signalizer_of_le_twoSectionCentralizer X M _ (S.isPGroup'.map _)
    (map_subtype_le _) (pCoreIn_le_sylow_twoSectionCentralizer X M hXM S)

/-- Restricting the section centralizer to an ambient subgroup is intersection. -/
theorem twoSectionCentralizer_eq_inf (X M : Subgroup G) :
    twoSectionCentralizer X M = M ⊓ twoSectionCentralizer X ⊤ := by
  ext g
  simp only [mem_twoSectionCentralizer, mem_inf, mem_top, true_and]

/-- If X is normal in M, its section centralizer is normal in M as well. -/
theorem twoSectionCentralizer_normalized (X M : Subgroup G)
    (hMX : M ≤ normalizer (X : Set G)) :
    M ≤ normalizer (twoSectionCentralizer X M : Set G) := by
  simpa only [inf_of_le_left hMX] using normalizer_twoSectionCentralizer X M

end CFSG.Quasithin.ChapterA.Section04

end
