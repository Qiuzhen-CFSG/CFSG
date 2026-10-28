module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.KernelRoot
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# Source C₂ commutators and the kernel lower bound

Assume the two canonical simple remainders are normal in U, the literal
hypotheses of Fong–Seitz I (3G). Intersections with conjugate remainders
put the adjacent-root commutator simultaneously in a simple root and
its disjoint remainder, so it is trivial. Weyl conjugation and the four
ordered positive roots then show that the exact (6A)(a) clause
[U₂,U₂^{s₁}]=1 makes U normalize U₂^{s₁}. If U₂ is abelian, the same
proof gives full centrality in U.

The actual coset-fixation theorem therefore gives the q-element kernel
lower bound without a permutation-fixation premise. Neither radical
normality nor row selection is silently inferred from m=4 or equal root
orders. Their final source discharge remains necessary. The argument
works at q=2 and does not require either local factor to be perfect.

Source: Fong–Seitz I (3G), pp.14–16, (6A)(a), pp.36–38;
II (7C), p.193. The literal source application is `SourceGeometry`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem longest_forms (hm : rotationOrder Q = 4) :
    longest Q = Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1 ∧
    longest Q = Q.simple 1*Q.simple 0*Q.simple 1*Q.simple 0 := by
  constructor
  · simpa only [hm,alternatingWord,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,Bool.not_true,mul_one,mul_assoc] using (alternatingWord_longest Q false).symm
  · simpa only [hm,alternatingWord,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,Bool.not_true,mul_one,mul_assoc] using (alternatingWord_longest Q true).symm

private theorem simple_squares (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

/-- The adjacent-root case of source (3G). Its hypotheses are precisely
normality in U of both original simple remainders. -/
theorem first_commutes_kernelRoot (hm : rotationOrder Q = 4)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D))) :
    ⁅simpleRoot Q split 0,kernelRoot Q split⁆ = ⊥ := by
  let A := simpleRoot Q split 0
  let K := kernelRoot Q split
  let W := unipotentConjugate split (Q.simple 0*Q.simple 1)
  let V := rightConjugate (simpleRemainder Q split 1)
    (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)
  have hA : A = split.U ⊓ unipotentConjugate split (Q.simple 1*Q.simple 0*Q.simple 1) := by
    dsimp only [A,simpleRoot,rootIntersection]
    rw [(longest_forms Q hm).2]
    simp only [mul_assoc,simple_squares,mul_one]
  have hK : K = unipotentConjugate split (Q.simple 0) ⊓ W :=
    kernelRoot_eq_intersection Q split hm
  have hVeq : V = W ⊓ unipotentConjugate split (Q.simple 1*Q.simple 0*Q.simple 1) := by
    dsimp only [V,simpleRemainder]
    rw [rightConjugate_inf,
      ← unipotentConjugate_eq split (Q.simple 0*Q.simple 1) (representative _) (representative_spec _),
      unipotentConjugate_right split _ _ (representative _) (representative_spec _)]
    simp only [W,mul_assoc]
  have hAW : A ≤ W := by
    apply (simpleRoot_le_ascent_intersection Q split (Q.simple 0*Q.simple 1) 0 ?_).trans inf_le_right
    have h2 := wordLength_alternatingWord Q false (n := 2) (by omega)
    have h3 := wordLength_alternatingWord Q false (n := 3) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,
      Bool.not_true,mul_one,← mul_assoc] at h2 h3
    rw [h2,h3]
  have hKW : K ≤ W := hK ▸ inf_le_right
  have hKU : K ≤ split.U := kernelRoot_le_unipotent Q split hm
  have hKV0 : K ≤ simpleRemainder Q split 0 := by
    exact le_inf hKU (hK ▸ inf_le_left)
  have hAV : A ≤ V := by
    rw [hVeq]
    exact le_inf hAW (hA ▸ inf_le_right)
  have hNV : W ≤ normalizer (V : Set (X ⧸ Q.D)) := by
    have h := (comap_mono (f := (MulAut.conj
      (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)).toMonoidHom) (hV 1)).trans
      (le_normalizer_comap (H := simpleRemainder Q split 1) _)
    dsimp only [W]
    rw [unipotentConjugate_eq split (Q.simple 0*Q.simple 1)
      (representative _) (representative_spec _)]
    exact h
  have hc0 : ⁅A,K⁆ ≤ simpleRemainder Q split 0 :=
    (commutator_mono (simpleRoot_le Q split 0) hKV0).trans
      (le_normalizer_iff_commutator_le_right.mp (hV 0))
  have hcV : ⁅A,K⁆ ≤ V :=
    (commutator_mono hAV hKW).trans (le_normalizer_iff_commutator_le_left.mp hNV)
  have hcA : ⁅A,K⁆ ≤ A := by
    exact (le_inf (hc0.trans inf_le_left)
      (hcV.trans (hVeq ▸ inf_le_right))).trans (le_of_eq hA.symm)
  exact le_bot_iff.mp ((le_inf hcA hc0).trans
    (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split 0) ▸ le_rfl))

private theorem otherRoot_conjugate_first (hm : rotationOrder Q = 4) :
    rightConjugate (rightConjugate (simpleRoot Q split 0)
      (representative (Q.simple 1) : X ⧸ Q.D))
      (representative (Q.simple 0) : X ⧸ Q.D) =
    rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D) := by
  have hK : rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D) =
      unipotentConjugate split (Q.simple 1) ⊓ unipotentConjugate split (Q.simple 1*Q.simple 0) := by
    rw [simpleRoot,rootIntersection,rightConjugate_inf,
      ← unipotentConjugate_eq split (Q.simple 1) (representative _) (representative_spec _),
      unipotentConjugate_right split _ _ (representative _) (representative_spec _),
      (longest_forms Q hm).2]
    simp only [mul_assoc,simple_squares,mul_one]
  rw [hK,rightConjugate_inf,
    unipotentConjugate_right split _ _ (representative _) (representative_spec _),
    unipotentConjugate_right split _ _ (representative _) (representative_spec _)]
  simp only [mul_assoc,simple_squares,mul_one,inf_comm]

private theorem kernelRoot_conjugate_first :
    rightConjugate (kernelRoot Q split) (representative (Q.simple 0) : X ⧸ Q.D) =
      simpleRoot Q split 1 := by
  rw [kernelRoot,← rightConjugate_mul]
  apply rightConjugate_eq_self
  apply torus_normalizes_simpleRoot Q split 1
  have h := Q.tits.representative_sq_mem_intersection (Q.simple_mem 0)
    (representative (Q.simple 0)) (representative_spec _)
  change (representative (Q.simple 0) : X ⧸ Q.D)^2 ∈ Q.tits.B ⊓ Q.tits.N at h
  simpa only [pow_two] using h

/-- The four canonical positive factors in the original orientation. -/
theorem four_root_product (hm : rotationOrder Q = 4) :
    (((simpleRoot Q split 0 : Set (X ⧸ Q.D)) * (kernelRoot Q split : Set (X ⧸ Q.D))) *
      (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D) :
        Set (X ⧸ Q.D))) * (simpleRoot Q split 1 : Set (X ⧸ Q.D)) = split.U := by
  have h := unipotent_ordered_product Q split false
  rw [hm] at h
  simp only [orderedRoots,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,
    List.map_cons,List.map_nil] at h
  dsimp at h
  simp only [List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at h
  change (simpleRoot Q split 0 : Set (X ⧸ Q.D)) *
    ((kernelRoot Q split : Set (X ⧸ Q.D)) *
      ((rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D))
        (representative (Q.simple 0) : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
        (rightConjugate (rightConjugate (kernelRoot Q split) (representative (Q.simple 1) : X ⧸ Q.D))
          (representative (Q.simple 0) : X ⧸ Q.D) : Set (X ⧸ Q.D)))) = _ at h
  rw [otherRoot_conjugate_first Q split hm,kernelRoot_conjugate_second Q split hm,
    kernelRoot_conjugate_first Q split] at h
  simpa only [mul_assoc] using h

private theorem conjugate_le {Y : Type*} [Group Y] {A H : Subgroup Y}
    (hAH : A ≤ H) {n : Y} (hn : n ∈ H) : rightConjugate A n ≤ H := by
  intro x hx
  change n*x*n⁻¹ ∈ A at hx
  have h := H.mul_mem (H.mul_mem (H.inv_mem hn) (hAH hx)) hn
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using h

/-- Source (6A)(a)'s exact commutation, together with (3G)'s two radical
normalities, makes the actual kernel root normal in U. No field equations
or abelianness of the root itself are required for this fixation argument. -/
theorem unipotent_normalizes_kernelRoot_of_row (hm : rotationOrder Q = 4)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    split.U ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
  have hA := (commutator_eq_bot_iff_le_centralizer.mp
    (first_commutes_kernelRoot Q split hm hV)).trans (centralizer_le_normalizer _)
  have hB := (commutator_eq_bot_iff_le_centralizer.mp hrow).trans (centralizer_le_normalizer _)
  have hK : kernelRoot Q split ≤ normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) := le_normalizer
  have hL := conjugate_le hA (second_normalizes_kernelRoot Q split hm)
  intro x hx
  change x ∈ (split.U : Set (X ⧸ Q.D)) at hx
  rw [← four_root_product Q split hm] at hx
  obtain ⟨y,⟨z,⟨a,ha,k,hk,rfl⟩,l,hl,rfl⟩,b,hb,rfl⟩ := hx
  exact mul_mem (mul_mem (mul_mem (hA ha) (hK hk)) (hL hl)) (hB hb)

/-- With the abelian second simple root supplied by the original linear
local quotient, the same argument proves the full centrality used in (7C). -/
theorem kernelRoot_central_of_row (hm : rotationOrder Q = 4)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥)
    [IsMulCommutative (simpleRoot Q split 1)] :
    split.U ≤ centralizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
  have hA := commutator_eq_bot_iff_le_centralizer.mp (first_commutes_kernelRoot Q split hm hV)
  have hB := commutator_eq_bot_iff_le_centralizer.mp hrow
  have habel : IsMulCommutative (kernelRoot Q split) :=
    (simpleRoot Q split 1).comap_injective_isMulCommutative (MulAut.conj
      (representative (Q.simple 0) : X ⧸ Q.D)).injective
  have hK := le_centralizer_iff_isMulCommutative.mpr habel
  have hNC : normalizer (kernelRoot Q split : Set (X ⧸ Q.D)) ≤
      normalizer (centralizer (kernelRoot Q split : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  have hL : rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D) ≤
      centralizer (kernelRoot Q split : Set (X ⧸ Q.D)) := by
    intro x hx
    exact (mem_normalizer_iff.mp (hNC (second_normalizes_kernelRoot Q split hm)) x).mpr (hA hx)
  intro x hx
  change x ∈ (split.U : Set (X ⧸ Q.D)) at hx
  rw [← four_root_product Q split hm] at hx
  obtain ⟨y,⟨z,⟨a,ha,k,hk,rfl⟩,l,hl,rfl⟩,b,hb,rfl⟩ := hx
  exact mul_mem (mul_mem (mul_mem (hA ha) (hK hk)) (hL hl)) (hB hb)

/-- All actual cosets in the source closed neighboring orbit are fixed
under the exact row commutation and the preceding radical normalities. -/
theorem kernelRoot_fixes_of_row (hm : rotationOrder Q = 4)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    ∀ u ∈ kernelRoot Q split, ∀ c ∈ insert (rightCosetPoint Q 1 1)
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)),
      u • c = c :=
  kernelRoot_fixes_closed_orbit Q split hm
    (unipotent_normalizes_kernelRoot_of_row Q split hm hV hrow)

/-- The source root of order q gives the full required kernel lower bound
on the actual second-parabolic neighboring orbit. -/
theorem source_kernel_lower_bound {q : ℕ} (hm : rotationOrder Q = 4)
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    q ≤ Nat.card (fixingSubgroup (X ⧸ Q.D) (insert (rightCosetPoint Q 1 1)
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)))) :=
  kernel_lower_bound Q split _ hq1 (kernelRoot_fixes_of_row Q split hm hV hrow)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
