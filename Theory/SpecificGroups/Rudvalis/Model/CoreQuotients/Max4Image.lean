module

public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Action
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.SurjectiveKernels
import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Image.BinaryCertificate
import Theory.ElementaryAbelian.AutomorphismCardEight
import Mathlib.Tactic.FinCases

/-!
# Full image of the actual Rudvalis max4 conjugation action

The eight products of the three original marked commuting involutions enumerate
`LocalCover.elementary 2` bijectively: binary expansion gives surjectivity and
its proved order eight gives injectivity. The checked max4 generator identities
therefore identify their actions with the two explicit binary maps in
`BinaryCertificate`. The certificate supplies 168 words with distinct triples
of basis images. Since the eight-group has exactly 168 automorphisms, the actual
conjugation action is surjective.

This discharges the full-image hypothesis in `SurjectiveKernels`: the literal
relative centralizer is the intrinsic two-core, and the intrinsic max4 quotient
is PSL₃(2), compatibly with its quotient projection and conjugation action.
No ambient Rudvalis order or simplicity theorem and no split-extension claim
is used. Source: GLS3 Table 5.3r and its justification, printed pp.291–292;
the quotient is an input to Aschbacher–Smith E.1.14(5), printed p.214.
All original ATLAS words, actions and attribution in the imported model are
preserved.
-/

open Subgroup
open Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open RankOneEightCharacteristic
open scoped IsMulCommutative

namespace Rudvalis.CoreQuotients

namespace Max4Image
local instance : IsElementaryAbelian 2 (elementary 2) := elementary_two_elementary
private def b (i : Fin 3) : elementary 2 := ⟨basis i, basis_mem i⟩
private theorem b_square (i : Fin 3) : b i * b i = 1 := Subtype.ext (basis_square i)
private theorem b_closure : closure (Set.range b) = ⊤ := by
  apply map_injective (elementary 2).subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact closure_basis
private def point : Fin 8 → elementary 2 :=
  ![1, b 0, b 1, b 0 * b 1, b 2, b 0 * b 2, b 1 * b 2, b 0 * b 1 * b 2]
private theorem point_surjective : Function.Surjective point := by
  intro x
  obtain ⟨c, hc⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range b b_square
    (show x ∈ closure (Set.range b) by rw [b_closure]; trivial)
  simp only [Fin.prod_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.prod_univ_zero, mul_one] at hc
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2
  all_goals simp only [h0, h1, h2, Bool.false_eq_true, ↓reduceIte,
    one_mul, mul_one] at hc
  · exact ⟨0, hc.symm⟩
  · exact ⟨4, hc.symm⟩
  · exact ⟨2, hc.symm⟩
  · exact ⟨6, hc.symm⟩
  · exact ⟨1, hc.symm⟩
  · exact ⟨5, hc.symm⟩
  · exact ⟨3, hc.symm⟩
  · exact ⟨7, by
      change b 0 * b 1 * b 2 = x
      simpa only [mul_assoc] using hc.symm⟩
private theorem point_injective : Function.Injective point :=
  ((Nat.bijective_iff_surjective_and_card point).mpr
    ⟨point_surjective, by rw [Nat.card_fin, elementary_two_card]⟩).1

private def gen : Fin 2 → max4 :=
  ![⟨max4Generators.1, subset_closure (by simp)⟩,
    ⟨max4Generators.2, subset_closure (by simp)⟩]
private theorem gen_basis :
    (∀ i : Fin 3, max4EightAction (gen 0) (b i) =
      ![b 0, b 0 * b 1 * b 2, b 2] i) ∧
    (∀ i : Fin 3, max4EightAction (gen 1) (b i) =
      ![b 0 * b 1, b 1 * b 2, b 1] i) := by
  constructor <;> intro i <;> fin_cases i <;> apply Subtype.ext
  · exact RankOneEightAction.first_conj_zero
  · exact RankOneEightAction.first_conj_one
  · exact RankOneEightAction.first_conj_two
  · exact RankOneEightAction.second_conj_zero
  · exact RankOneEightAction.second_conj_one
  · exact RankOneEightAction.second_conj_two
private theorem gen_point (g : Fin 2) (x : Fin 8) :
    max4EightAction (gen g) (point x) = point (BinaryCertificate.step g x) := by
  have cancel (i : Fin 3) (x : elementary 2) : b i * (b i * x) = x := by
    rw [← mul_assoc, b_square, one_mul]
  fin_cases g <;> fin_cases x <;>
    simp [point, BinaryCertificate.step, map_mul, gen_basis.1, gen_basis.2, b_square,
      mul_left_comm, mul_comm, cancel]

private def word : List (Fin 2) → max4
  | [] => 1
  | g :: w => gen g * word w

private theorem word_point (w : List (Fin 2)) (x : Fin 8) :
    max4EightAction (word w) (point x) = point (BinaryCertificate.act w x) := by
  induction w with
  | nil => simp [word, BinaryCertificate.act]
  | cons g w ih =>
    rw [word, map_mul, MulAut.mul_apply, ih, gen_point]
    rfl

private def imageWord (i : Fin 168) : max4EightAction.range :=
  ⟨max4EightAction (word (BinaryCertificate.words i)), ⟨_, rfl⟩⟩

private theorem imageWord_injective : Function.Injective imageWord := by
  intro i j h
  apply BinaryCertificate.signature_injective
  have hp (x : Fin 8) : BinaryCertificate.act (BinaryCertificate.words i) x =
      BinaryCertificate.act (BinaryCertificate.words j) x := by
    apply point_injective
    rw [← word_point, ← word_point]
    exact congrArg (fun a : max4EightAction.range => a.val (point x)) h
  exact Prod.ext (hp 1) (Prod.ext (hp 2) (hp 4))

end Max4Image

/-- The marked max4 subgroup induces every automorphism of its actual eight-group. -/
public theorem max4EightAction_surjective : Function.Surjective max4EightAction := by
  let := RankOneEightCharacteristic.elementary_two_elementary
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_le_card
  have h := Nat.card_le_card_of_injective Max4Image.imageWord Max4Image.imageWord_injective
  rw [Nat.card_fin] at h
  rwa [card_mulAut_of_elementary_eight (elementary 2)
    RankOneEightCharacteristic.elementary_two_card]

/-- The actual max4 action surjects onto the project's binary PSL₃(2) model. -/
public theorem max4LinearAction_surjective : Function.Surjective max4LinearAction :=
  max4LinearAction_surjective_of_eightAction max4EightAction_surjective

/-- The kernel of the actual matrix action is the intrinsic two-core. -/
public theorem max4LinearAction_ker_eq_pCore :
    max4LinearAction.ker = pCore 2 max4 :=
  max4_kernel_eq_pCore max4LinearAction max4LinearAction_surjective

/-- The kernel of the marked eight-group action is the intrinsic two-core. -/
public theorem max4EightAction_ker_eq_pCore :
    max4EightAction.ker = pCore 2 max4 := by
  rw [← max4LinearAction_ker, max4LinearAction_ker_eq_pCore]

/-- The relative centralizer of the marked eight-group in max4 is its two-core. -/
public theorem max4_centralizer_eq_pCore :
    (centralizer (elementary 2 : Set Model)).subgroupOf max4 = pCore 2 max4 := by
  rw [← max4EightAction_ker, max4EightAction_ker_eq_pCore]

/-- The intrinsic max4 quotient, identified by the actual conjugation action. -/
public noncomputable def max4QuotientEquiv :
    (max4 ⧸ pCore 2 max4) ≃* Matrix.PSL3Two.PSL :=
  max4QuotientEquivOfSurjective max4LinearAction max4LinearAction_surjective

/-- The quotient equivalence preserves the literal quotient projection and action. -/
@[simp] public theorem max4QuotientEquiv_mk (g : max4) :
    max4QuotientEquiv (QuotientGroup.mk' (pCore 2 max4) g) = max4LinearAction g :=
  max4QuotientEquivOfSurjective_mk _ _ g

end Rudvalis.CoreQuotients
