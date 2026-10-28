module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.OrderFour
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.Alternating.FiveComponents
public import CFSG.Quasithin.ClassicalModels
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Locating the marked PSL₂ component in a classified FF actor

A component contained in a quasisimple actor is the whole actor, by the
ordinary component calculus. The rank-two actor is large enough for this
argument because the marked PSL₂ component has order at least sixty.
Its order polynomial recovers the field exponent. A unipotent Jordan block
of size three has order four, excluding every rank-three actor: even-field
PSL₂ has no element of that order.

For S₅, perfectness puts the marked component in its actual alternating
subgroup. The existing A₅ component equivalence supplies its order, so
containment is equality. The same order polynomial then gives n = 2.
These comparisons use the actor's supplied equivalence and retain its
marked subgroup image, not just an abstract isomorphic group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 13.8.16(1), p.952 (PDF p.969). Matrix simplicity
and order are reused from the attributed ATLAS ports named in the imports.
-/

public section

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons

private theorem component_eq_of_quasisimple {D : Type*} [Group D]
    {A C : Subgroup D} (hA : IsComponent D A) (hAC : A ≤ C)
    [IsQuasisimple C] : A = C := by
  have ht : IsComponent C ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv (topEquiv).symm⟩
  exact le_antisymm hAC (subgroupOf_eq_top.mp ((hA.subgroupOf hAC).eq_of_le ht le_top))

private theorem order_polynomial_strictMono :
    StrictMonoOn (fun q : ℕ => q * (q ^ 2 - 1)) (Set.Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [show 2 ≤ x from hx]
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_left (show x ^ 2 - 1 < y ^ 2 - 1 by omega)
    (show 0 < x by omega)
  have hle := Nat.mul_le_mul_right (y ^ 2 - 1) (Nat.le_of_lt hxy)
  exact hmul.trans_le hle

private theorem psl_card {A : Type*} [Group A] {n : ℕ}
    (h : ClassicalGroup.IsPSL A 2 (2 ^ n)) :
    Nat.card A = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).toEquiv,
    Atlas.card_sl_two, hF]

private theorem psl_card_ge_sixty {A : Type*} [Group A] {n : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSL A 2 (2 ^ n)) : 60 ≤ Nat.card A := by
  rw [psl_card h]
  have hp : 4 ≤ 2 ^ n := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  exact order_polynomial_strictMono.monotoneOn (show 2 ≤ 4 by decide) (show 2 ≤ 2 ^ n by omega) hp

/-- The actual marked component fills a rank-two actor, with the field exponent retained. -/
theorem linearTwo {D : Type*} [Group D] [Finite D] {A C : Subgroup D}
    (hA : IsComponent D A) (hAC : A ≤ C) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL A 2 (2 ^ n)) (F : BinaryField)
    (e : C ≃* SL(2,F.Carrier)) : A = C ∧ F.degree = n := by
  have hpos := F.degree_pos
  have hlarge : 60 ≤ Nat.card C := (psl_card_ge_sixty hn hmodel).trans
    (Nat.card_le_card_of_injective (inclusion hAC) (inclusion_injective hAC))
  have hcardC : Nat.card C = Nat.card F.Carrier * (Nat.card F.Carrier ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans Atlas.card_sl_two
  have hfour : 4 ≤ Nat.card F.Carrier := by
    have hp : 2 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.le_self_pow (by omega) 2
    by_contra h
    have hs : Nat.card F.Carrier = 2 ∨ Nat.card F.Carrier = 3 := by omega
    rcases hs with hs | hs <;> rw [hs] at hcardC <;> omega
  let es : SL(2,F.Carrier) ≃* PSL(2,F.Carrier) :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : Group.IsPerfect PSL(2,F.Carrier) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F.Carrier (by omega)
  let : Group.IsPerfect SL(2,F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := es.symm.toMonoidHom) es.symm.surjective
  let : IsQuasisimple SL(2,F.Carrier) :=
    { toIsPerfect := inferInstance
      simple := inferInstance }
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  have heq : A = C := component_eq_of_quasisimple hA hAC
  refine ⟨heq, ?_⟩
  have hcard := psl_card hmodel
  rw [heq, hcardC, F.card_eq] at hcard
  apply Nat.pow_right_injective (by decide : 1 < 2)
  exact order_polynomial_strictMono.injOn
    (show 2 ≤ 2 ^ F.degree from Nat.le_self_pow (by omega) 2)
    (show 2 ≤ 2 ^ n from Nat.le_self_pow (by omega) 2) hcard

private theorem sl_three_order_four (F : Type*) [Field F] [CharP F 2] :
    ∃ g : SL(3,F), orderOf g = 4 := by
  let g : SL(3,F) := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  have hs : g ^ 2 ≠ 1 := by
    intro h
    have he := congrArg (fun x : SL(3,F) => x.val 0 2) h
    change ((!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 2) 0 2 = 0 at he
    simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three] at he
    change (1 : F) * 0 + 1 * 1 + 0 * 1 = 0 at he
    simp at he
  have hf : g ^ 4 = 1 := by
    apply Subtype.ext
    change (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 4 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  exact ⟨g, orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hs) (by simpa using hf)⟩

/-- No rank-three actor can contain the marked rank-one component. -/
theorem not_linearThree {D : Type*} [Group D] {A C : Subgroup D}
    (hA : IsComponent D A) (hAC : A ≤ C) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL A 2 (2 ^ n)) (F : BinaryField)
    (e : C ≃* SL(3,F.Carrier)) : False := by
  let : IsQuasisimple SL(3,F.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  have heq : A = C := component_eq_of_quasisimple hA hAC
  obtain ⟨K, _, _, hK, ⟨ek⟩⟩ := hmodel
  let _ := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  obtain ⟨g, hg⟩ := sl_three_order_four F.Carrier
  exact F918Sections.NoStrong.not_equiv_psl_of_order_four g hg
    ⟨ek.symm.trans ((MulEquiv.subgroupCongr heq).trans e)⟩

/-- The permutation equivalence carries the literal marked component to A₅. -/
theorem symmetricFive {D : Type*} [Group D] {A C : Subgroup D}
    (hA : IsComponent D A) (hAC : A ≤ C) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL A 2 (2 ^ n))
    (e : C ≃* Equiv.Perm (Fin 5)) :
    (A.subgroupOf C).map e.toMonoidHom = alternatingGroup (Fin 5) ∧ n = 2 := by
  let B := (A.subgroupOf C).map e.toMonoidHom
  have hB : IsComponent _ B := (hA.subgroupOf hAC).map_equiv e
  let := hB.2
  have hle : B ≤ alternatingGroup (Fin 5) :=
    le_of_isPerfect_of_index_eq_two B _ alternatingGroup.index_eq_two
  obtain ⟨eb⟩ := component_symmetric_five_equiv B hB
  have hb : B = alternatingGroup (Fin 5) :=
    eq_of_le_of_card_ge hle (Nat.card_congr eb.toEquiv).ge
  refine ⟨hb, ?_⟩
  let ea : A ≃* alternatingGroup (Fin 5) :=
    ((subgroupOfEquivOfLe hAC).symm.trans (e.subgroupMap (A.subgroupOf C))).trans eb
  have hc : Nat.card A = 60 := by
    rw [Nat.card_congr ea.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hq : 2 ^ n = 2 ^ 2 := by
    apply order_polynomial_strictMono.injOn
      (show 2 ≤ 2 ^ n from Nat.le_self_pow (by omega) 2) (by decide)
    simpa [psl_card hmodel] using hc
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hq
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.GroupComparisons
