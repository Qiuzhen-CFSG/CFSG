module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
/-!
# The derived subgroup of the central HS involution centralizer

Five checked identities express the exact pair-kernel generators as products
of at most two commutators. The full kernel therefore lies in the derived
subgroup. Its actual S₅ quotient identifies the derived index as two and
its order as 3840. This calculation supplies the central-cover bound used
in E.6.23; it assumes neither a split extension nor fixed-point lifting.

The import of private pair-action witnesses is an internal proof extension;
all public statements concern the original group and its derived subgroup.
Source: GLS3 Table 5.3m; Aschbacher–Smith 16.1.5(10), p.1172, and E.6.23,
p.254. The ATLAS carrier and action conventions are unchanged.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.DerivedCentralizer
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open CentralInvolutionCore CoreStructure
open CentralNormalizerThreePart.PairQuotient
set_option maxRecDepth 10000

def localGenerator (i : Fin 7) : localGroup 0 :=
  if h : i.val < 5 then (qElement ⟨i.val,h⟩).val
  else if i.val = 5 then swapLocal else cycleLocal

def commutatorWord : Fin 5 → List (Fin 49) := ![[13], [5,45], [5,42], [34], [5]]
def commutatorLetter (i : Fin 49) : localGroup 0 :=
  ⁅localGenerator ⟨i.val / 7, by omega⟩, localGenerator ⟨i.val % 7, Nat.mod_lt _ (by decide)⟩⁆

theorem q_word : ∀ i, evalWord commutatorLetter (commutatorWord i) = (qElement i).val := by
  intro i
  apply Subtype.ext
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 5, ∀ p : Fin 100,
      inclusion (evalWord commutatorLetter (commutatorWord i)).val p =
        inclusion (qElement i).val.val p := by
    apply CentralInvolutionCore.allFin
    decide +kernel
  exact h i

theorem q_mem_derived (i : Fin 5) : (qElement i).val ∈ commutator (localGroup 0) := by
  rw [← q_word i]
  have h : ∀ w : List (Fin 49), evalWord commutatorLetter w ∈ commutator (localGroup 0) := by
    intro w
    induction w with
    | nil => exact one_mem _
    | cons j w ih =>
      apply mul_mem _ ih
      exact commutator_mem_commutator (mem_top _) (mem_top _)
  exact h _
theorem core_le_derived : core ≤ commutator (localGroup 0) := by
  let N := (commutator (localGroup 0)).comap core.subtype
  have hq (i : Fin 5) : qElement i ∈ N := q_mem_derived i
  have hlI : leftI ∈ N := N.mul_mem (hq 0) (hq 2)
  have hlJ : leftJ ∈ N := N.mul_mem (hq 1) (hq 3)
  have hrI : rightI ∈ N := N.mul_mem (hq 0) (hq 3)
  have hrJ : rightJ ∈ N := N.mul_mem (N.mul_mem (hq 0) (hq 1)) (hq 2)
  have hc : cyclicGenerator ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hq 0) (hq 1)) (hq 2)) (hq 3)) (hq 4)
  have hleft : leftFactor ≤ N := by
    rintro _ ⟨q, rfl⟩
    cases q with
    | a i => exact N.pow_mem hlI _
    | xa i => exact N.mul_mem hlJ (N.pow_mem hlI _)
  have hright : rightFactor ≤ N := by
    rintro _ ⟨q, rfl⟩
    cases q with
    | a i => exact N.pow_mem hrI _
    | xa i => exact N.mul_mem hrJ (N.pow_mem hrI _)
  have hcyclic : cyclicPart ≤ N := by
    rintro _ ⟨n, rfl⟩
    exact N.pow_mem hc _
  have hspan : embeddedCore ≤ N := sup_le (sup_le hleft hright) hcyclic
  have he : embeddedCore = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top, embeddedCore_card]
    exact core_card_le)
  rw [he] at hspan
  intro x hx
  exact hspan (show (⟨x, hx⟩ : core) ∈ ⊤ from trivial)

theorem derived_index : (commutator (localGroup 0)).index = 2 := by
  have hm : (commutator (localGroup 0)).map fiveHom = alternatingGroup (Fin 5) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr fiveHom_surjective,
      ← commutator_def, alternatingGroup.commutator_perm_eq (by simp)]
  have hc : (alternatingGroup (Fin 5)).comap fiveHom = commutator (localGroup 0) := by
    rw [← hm, comap_map_eq, fiveHom_kernel, sup_eq_left.mpr core_le_derived]
  rw [← hc, index_comap_of_surjective _ fiveHom_surjective]
  exact alternatingGroup.index_eq_two

theorem derived_card : Nat.card (commutator (localGroup 0)) = 3840 := by
  have hL : Nat.card (localGroup 0) = 7680 :=
    (Nat.card_congr (MulEquiv.subgroupCongr localGroup_zero_eq_centralizer).toEquiv).trans
      centralizer_card
  have hh := (commutator (localGroup 0)).card_mul_index
  rw [derived_index, hL] at hh
  omega

theorem centralizer_derived_card :
    Nat.card (commutator (centralizer ({e0} : Set Carrier))) = 3840 := by
  let e := MulEquiv.subgroupCongr localGroup_zero_eq_centralizer
  have hm : (commutator (localGroup 0)).map e.toMonoidHom =
      commutator (centralizer ({e0} : Set Carrier)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]
  have hc := card_map_of_injective (f := e.toMonoidHom) (K := commutator (localGroup 0)) e.injective
  rw [hm] at hc
  exact hc.trans derived_card

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.DerivedCentralizer
