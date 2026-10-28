module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Validity.Base
/-!
# Interpreting checked word deductions in the original carrier

Natural-number letters keep the computational word identities small. Their
interpretation is the literal original generator, modulo the alphabet size;
`eval_toNatWord` identifies this with the original finite alphabet. Source,
forward and reverse deduction lemmas then yield ordinary Lean proof terms.
See `source/README.md` for the ATLAS provenance and exact certificate.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.ValidityCertificate
open Subgroup.CosetWordCertificate

abbrev NatWord := Word Nat

def natGenerator (n : Nat) : Schreier.Carrier :=
  localGenerator ⟨n % 101, Nat.mod_lt _ (by decide)⟩

def toNatWord (w : W) : NatWord := w.map (fun a => (a.1.val, a.2))

theorem eval_toNatWord (w : W) : eval natGenerator (toNatWord w) = eval localGenerator w := by
  have h : natGenerator ∘ (Fin.val : Fin 101 → Nat) = localGenerator := by
    funext i
    simp only [Function.comp_apply, natGenerator, Nat.mod_eq_of_lt i.isLt]
  unfold toNatWord
  rw [eval_map_letters, h]

def rawNatRelator (r : Nat) : NatWord := toNatWord (rawRelator r)

theorem rawNatRelator_valid (r : Nat) : eval natGenerator (rawNatRelator r) = 1 := by
  rw [rawNatRelator, eval_toNatWord]
  exact rawRelator_valid r

def Valid (w : NatWord) : Prop := eval natGenerator w = 1

theorem valid_empty : Valid [] := eval_nil _

theorem valid_source (r cut : Nat) (w : NatWord)
    (hc : normalize (rawNatRelator r) cut = w) : Valid w := by
  rw [← hc]
  exact (normalize_one_iff _ _ _).mpr (rawNatRelator_valid r)

theorem valid_forward (w r v : NatWord) (a b c : Nat) (positive : Bool)
    (hw : Valid w) (hr : Valid r)
    (hc : transform w r a b c positive = v) : Valid v := by
  rw [← hc]
  exact (transform_one_iff _ _ _ _ _ _ _ hr).mpr hw

theorem valid_backward (w r v : NatWord) (a b c : Nat) (positive : Bool)
    (hv : Valid v) (hr : Valid r)
    (hc : transform w r a b c positive = v) : Valid w := by
  apply (transform_one_iff _ _ _ a b c positive hr).mp
  rw [hc]
  exact hv

theorem branch_valid (cutoff : Nat) {left right : Nat → NatWord}
    (hl : ∀ n, Valid (left n)) (hr : ∀ n, Valid (right n)) :
    ∀ n, Valid (branch cutoff left right n) := by
  intro n
  unfold branch
  split
  · exact hl n
  · exact hr n

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.ValidityCertificate
