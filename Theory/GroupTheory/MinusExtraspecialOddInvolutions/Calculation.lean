module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation
/-!
# Involution lifts over transpositions in the minus extraspecial model

For an automorphism a inducing a transposition on the five singular central
cosets, and d with a² = conjugation by d and a(d) = d, the norm equation
q a(q) d = 1 has a solution. Thus a lift of that transposition in any group
extension can be corrected to an involution in the same core coset.
An involutory transposition automorphism fixes exactly eight core elements.
The checked five-bit calculation uses the existing quaternion–dihedral
multiplication and prunes generator tuples by their defining relations.

Source application: Aschbacher–Smith 14.2.17(1), printed pp.986–987.
This is the involution-lifting step, not the full Sylow-centralizer geometry.
-/
@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.OddInvolution
open Outside

def squareInner (u v r s d : B) : Bool :=
  gens.all fun x => word u v r s (word u v r s x) == conj d x

def fixedCount (u v r s : B) : Nat :=
  all.countP fun x => word u v r s x == x

def calculation (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → moved u v r s = 2 →
  (∀ d : B, word u v r s d = d → squareInner u v r s d →
    ∃ q : B, mul (mul q (word u v r s q)) d = 0) ∧
  (Outside.invol u v r s → fixedCount u v r s = 8)
def certificate (u v r s : B) : Bool :=
  (all.all fun d => word u v r s d != d || !squareInner u v r s d ||
    (all.any fun q => mul (mul q (word u v r s q)) d == 0)) &&
  (!Outside.invol u v r s || fixedCount u v r s == 8)

def checked (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → moved u v r s = 2 → certificate u v r s
set_option synthInstance.maxSize 1024 in
instance (u : B) : Decidable (checked u) := by unfold checked; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked_all : ∀ u : B, checked u := by decide +kernel

theorem calculation_all : ∀ u : B, calculation u := by
  intro u h1 v h2 h3 r h4 h5 h6 s h7 h8 h9 h10 hm
  have hh := checked_all u h1 v h2 h3 r h4 h5 h6 s h7 h8 h9 h10 hm
  simp only [certificate, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hh
  refine ⟨?_,?_⟩
  · intro d hd hi
    have hm : d ∈ all := (show ∀ x : B, x ∈ all by decide +kernel) d
    have hn := List.all_eq_true.mp hh.1 d hm
    simp only [Bool.or_eq_true,bne_iff_ne,Bool.not_eq_true',hd,ne_eq,not_true_eq_false,
      false_or,hi,Bool.true_eq_false] at hn
    obtain ⟨q,_,hq⟩ := List.any_eq_true.mp hn
    exact ⟨q,by simpa only [beq_iff_eq] using hq⟩
  · intro hi
    exact hh.2.resolve_left (by rw [hi]; decide)
end MinusExtraspecial.FixedFourCalculation.OddInvolution
