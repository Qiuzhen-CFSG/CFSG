module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Data

/-!
# Restricting central Rudvalis normal forms

Among the 16384 certified binary products, only indices 0 and 6144 can
commute with generators 0, 1 and 2 on both points 0 and 1. This necessary
condition for centrality is checked by kernel reduction in eight bounded
batches. No permutation tables are added: the calculation uses the existing
point maps, whose connection to the original words is proved in LocalOrder.Maps.

The mathematical consumer is `SylowCenter.candidate_center_card_le_two`.
Source: the ATLAS degree-4060 action and RuG1-max4W1 words, attributed in
SylowOvergroups.RadicalCoverage.Sylow.Candidate and its LocalOrder descendants;
GLS3 Table 5.3r, printed p.279. The finite check uses no group-shape premise.
-/

namespace Rudvalis.SylowCenter.Certificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

private def centerTest (n : Fin 16384) : Prop :=
  (normalMap n (generatorMap 0 0) = generatorMap 0 (normalMap n 0) ∧
   normalMap n (generatorMap 0 1) = generatorMap 0 (normalMap n 1) ∧
   normalMap n (generatorMap 1 0) = generatorMap 1 (normalMap n 0) ∧
   normalMap n (generatorMap 1 1) = generatorMap 1 (normalMap n 1) ∧
   normalMap n (generatorMap 2 0) = generatorMap 2 (normalMap n 0) ∧
   normalMap n (generatorMap 2 1) = generatorMap 2 (normalMap n 1)) →
  n.val = 0 ∨ n.val = 6144

private instance (n : Fin 16384) : Decidable (centerTest n) :=
  inferInstanceAs (Decidable (_ → _))

private def checkBlock (b : Nat) : Bool :=
  Data.checkNat (fun k => decide
    (centerTest ⟨(2048 * b + k) % 16384, Nat.mod_lt _ (by decide)⟩)) 2048

-- The complete sequential check peaks at about 2.2 GB; avoid multiplying
-- the batches' memory requirements within the same compiler process.
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem block0 : checkBlock 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block1 : checkBlock 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block2 : checkBlock 2 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block3 : checkBlock 3 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block4 : checkBlock 4 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block5 : checkBlock 5 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block6 : checkBlock 6 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem block7 : checkBlock 7 = true := by decide +kernel

private theorem blocks (b : Fin 8) : checkBlock b.val = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨
      b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7

private theorem checkNat_sound (f : Nat → Bool) (n : Nat) :
    Data.checkNat f n = true → ∀ k < n, f k = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Data.checkNat, Bool.and_eq_true]
    rintro ⟨hn, hfn⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact ih hn k hlt
    · exact hfn

private theorem all_tests (n : Fin 16384) : centerTest n := by
  have hb : n.val / 2048 < 8 := by omega
  have h := of_decide_eq_true (checkNat_sound _ _
    (blocks ⟨n.val / 2048, hb⟩) (n.val % 2048) (Nat.mod_lt _ (by decide)))
  have he : (2048 * (n.val / 2048) + n.val % 2048) % 16384 = n.val := by omega
  simpa only [he] using h

/-- Commuting with the actual generator maps forces one of two normal forms.
Only six necessary point equations are used in the certificate. -/
public theorem index_eq_of_point_commutation (n : Fin 16384)
    (h : ∀ (i : Fin 14) (x : Fin 4060),
      normalMap n (generatorMap i x) = generatorMap i (normalMap n x)) :
    n.val = 0 ∨ n.val = 6144 :=
  all_tests n ⟨h 0 0, h 0 1, h 1 0, h 1 1, h 2 0, h 2 1⟩

end Rudvalis.SylowCenter.Certificate
