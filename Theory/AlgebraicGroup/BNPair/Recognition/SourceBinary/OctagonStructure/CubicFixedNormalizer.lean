module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleClosure
/-!
# Normalizers of the cubic fixed subgroup

For a coprime action on a finite solvable group, an abelian fixed subgroup
has equal relative normalizer and centralizer. The three-subgroups lemma
puts the normalizer's displacement subgroup in the centralizer; coprime
decomposition supplies the remaining fixed factor.

In the octagon this applies to the literal three odd roots fixed by the
separating cubic Cartan element. In the binary proper-centralizer branch,
their normalizer contains the elementary middle-root normal closure and
lies in the five middle roots. The middle-root orbit and cubic congruence
leave orders 32 and 128. At order 32 the normalizer equals the normal
closure, so it contains the fixed subgroup and centralizes all five roots.
This forces all five roots into the normalizer, a contradiction. Thus the
normalizer, and also the centralizer, equals the five-root subgroup.

Source: Fong--Seitz I (1973), (6G), printed p.50, normalizer argument.
This proves normalizer control, not the outstanding index-sixteen
exclusion or the terminal contradiction. Original-factor and Chapter 12
applications are in LinearPairCubicNormalizerSource and
SourceSelection/LinearPairCubicNormalizerChapter12.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup
/-- An abelian coprime fixed subgroup has no nontrivial automizer inside
the acted-on solvable group. Both intersections are in the ambient group. -/
theorem normalizer_fixed_eq_centralizer_fixed
    {Y : Type*} [Group Y] [Finite Y] (V T : Subgroup Y)
    (hTV : T ≤ normalizer (V : Set Y)) (hsol : Group.IsSolvable V)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card V))
    (hab : IsMulCommutative (V ⊓ centralizer (T : Set Y) : Subgroup Y)) :
    V ⊓ normalizer ((V ⊓ centralizer (T : Set Y) : Subgroup Y) : Set Y) =
      V ⊓ centralizer ((V ⊓ centralizer (T : Set Y) : Subgroup Y) : Set Y) := by
  let M := V ⊓ centralizer (T : Set Y)
  let N := V ⊓ normalizer (M : Set Y)
  let := hab
  let := hsol
  have hTM : T ≤ centralizer (M : Set Y) := le_centralizer_iff.mp inf_le_right
  have hTN : T ≤ normalizer (N : Set Y) :=
    (le_inf hTV ((hTM.trans (centralizer_le_normalizer _)).trans
      (normalizer (M : Set Y)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hNTM : ⁅N,T⁆ ≤ centralizer (M : Set Y) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_eq_bot_iff_le_centralizer.mpr hTM,commutator_bot_left]
    · exact bot_unique ((commutator_mono
        (le_normalizer_iff_commutator_le_left.mp (show N ≤ normalizer (M : Set Y) from inf_le_right))
        le_rfl).trans (commutator_eq_bot_iff_le_centralizer.mpr
          (le_centralizer_iff.mp hTM)).le)
  have hNM : N ⊓ centralizer (T : Set Y) ≤ M := inf_le_inf_right _ inf_le_left
  have hs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (show N ≤ V from inf_le_left))
  have hc : Nat.Coprime (Nat.card T) (Nat.card N) :=
    hcop.of_dvd_right (card_dvd_of_le (show N ≤ V from inf_le_left))
  have he := eq_commutator_sup_centralizer_of_solvable_coprime N T hTN hs hc
  apply le_antisymm
  · change N ≤ V ⊓ centralizer (M : Set Y)
    apply le_inf inf_le_left
    change N ≤ centralizer (M : Set Y)
    rw [he]
    exact sup_le hNTM (hNM.trans (le_centralizer M))
  · exact inf_le_inf_left _ (centralizer_le_normalizer _)
end Subgroup

open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The three literal odd roots forming the cubic fixed radical. -/
@[expose] def fixedOddRoots (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  rootAt Q split i (Q.simple j) ⊔
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
    rootAt Q split i (Q.simple j*Q.simple i)

/-- Normalizer and centralizer of the actual cubic fixed radical coincide. -/
theorem separated_fixedOddRoots_normalizer
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (s : RootReflection Q split i)
    {a : ℕ} (ha : 0 < a) (hF : Nat.card F = 2^a)
    (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc3 : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      simpleRemainder Q split i ⊓ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) := by
  let V := simpleRemainder Q split i
  let T := zpowers (c : X ⧸ Q.D)
  have hTV : T ≤ normalizer (V : Set (X ⧸ Q.D)) := zpowers_le.mpr
    (remainder_parabolic_normalizes Q split i hKi
      (Q.tits.B_le_standardParabolic _ c.property.1))
  have hVp : IsPGroup 2 V := split.sylow.isPGroup'.of_injective
    (inclusion (show V ≤ split.U from inf_le_left)) (inclusion_injective _)
  have hcop : Nat.Coprime (Nat.card T) (Nat.card V) := by
    obtain ⟨k,hk⟩ := hVp.exists_card_eq
    rw [show Nat.card T = 3 by rw [Nat.card_zpowers,orderOf_coe,hc3],hk]
    exact Nat.Coprime.pow_right k (by decide)
  have hab := (separated_linear_radical_abelian Q split hm i j hij hKi μi s
    ha hF hi c hc).1
  have he : fixedOddRoots Q split i j = V ⊓ centralizer (T : Set (X ⧸ Q.D)) := by
    dsimp only [T]
    rw [zpowers_eq_closure,centralizer_closure]
    exact separated_radical_centralizer_sup Q split hm i j hij c hc
  rw [he]
  apply normalizer_fixed_eq_centralizer_fixed V T hTV
    (@IsNilpotent.to_isSolvable V _ hVp.isNilpotent) hcop
  have hh : V ⊓ centralizer (T : Set (X ⧸ Q.D)) =
      V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
    dsimp only [T]
    rw [zpowers_eq_closure,centralizer_closure]
  exact (congrArg (fun D : Subgroup (X ⧸ Q.D) => IsMulCommutative D) hh).mpr hab

/-- The proper-centralizer branch restricts the actual fixed-subgroup
normalizer to orders 32 and 128 inside the five-root subgroup. -/
theorem separated_binary_fixedOddRoots_normalizer_card
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (s : RootReflection Q split i)
    (hF : Nat.card F = 2)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc3 : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hCJ : middleRootCentralizer Q split i j = middleFive Q split i j) :
    let N := simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D))
    middleRootClosure Q split i j ≤ N ∧ N ≤ middleFive Q split i j ∧
      (Nat.card N = 32 ∨ Nat.card N = 128) := by
  let V := simpleRemainder Q split i
  let M := fixedOddRoots Q split i j
  let J := middleFive Q split i j
  let N := V ⊓ normalizer (M : Set (X ⧸ Q.D))
  have hNC : N = V ⊓ centralizer (M : Set (X ⧸ Q.D)) :=
    separated_fixedOddRoots_normalizer Q split hm i j hij hKi μi s
      (a := 1) (by decide) hF hi c hc3 hc
  have hMJ : M ≤ J := sup_le
    (sup_le (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))) le_sup_right
  have hNJ : N ≤ J := by
    rw [hNC]
    change V ⊓ centralizer (M : Set _) ≤ middleFive Q split i j
    rw [←hCJ]
    exact inf_le_inf_left _ (centralizer_le (show
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ M from
        le_sup_of_le_left le_sup_right))
  have hJC : J ≤ middleRootCentralizer Q split i j := hCJ.ge
  have hEJ := middleRootClosure_le_middle_center Q split hm i j hij hKj hJC
  have hEN : middleRootClosure Q split i j ≤ N := by
    rw [hNC]
    exact le_inf ((hEJ.trans inf_le_left).trans (middleFive_le_remainder Q split hm i j hij))
      ((hEJ.trans inf_le_right).trans (centralizer_le hMJ))
  have hindex : (middleRootCentralizer Q split i j).relIndex V = 16 := by
    rw [hCJ]
    exact binary_middleFive_quotient_card Q split hm i j hij hi hj
  have h32 : 32 ≤ Nat.card N :=
    ((binary_middleRootClosure_card_bounds Q split hm i j hij hKj hi hj hJC).2.2 hindex).trans
      (card_le_of_le hEN)
  have hJcard : Nat.card J = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
  have hd : Nat.card N ∣ 128 := hJcard ▸ card_dvd_of_le hNJ
  have hM : M = V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :=
    separated_radical_centralizer_sup Q split hm i j hij c hc
  have hMcard : Nat.card M = 8 := by
    rw [hM]
    simpa only [hi,Nat.reducePow] using (octagon_separated_root_centralizer_orders Q split hm i j hij c hc).1
  have hMN : M ≤ N := le_inf (hMJ.trans (middleFive_le_remainder Q split hm i j hij)) M.le_normalizer
  have hfix : N ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = M :=
    le_antisymm (hM ▸ inf_le_inf_right _ inf_le_left) (le_inf hMN (hM ▸ inf_le_right))
  have hcM : (c : X ⧸ Q.D) ∈ centralizer (M : Set (X ⧸ Q.D)) :=
    by
      intro x hx
      exact (mem_centralizer_singleton_iff.mp ((hM.le hx).2))
  have hn : (c : X ⧸ Q.D) ∈ normalizer (N : Set (X ⧸ Q.D)) :=
    inf_normalizer_le_normalizer_inf ⟨remainder_parabolic_normalizes Q split i hKi
      (Q.tits.B_le_standardParabolic _ c.property.1),
      (normalizer (M : Set (X ⧸ Q.D))).le_normalizer (Subgroup.centralizer_le_normalizer _ hcM)⟩
  have hp : IsPGroup 3 (zpowers (c : X ⧸ Q.D)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,orderOf_coe,hc3]; rfl)
  have hmod := card_modEq_card_inf_centralizer (zpowers (c : X ⧸ Q.D)) N hp (zpowers_le.mpr hn)
  rw [zpowers_eq_closure,centralizer_closure,hfix,hMcard] at hmod
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (show Nat.card N ∣ 2^7 from hd)
  refine ⟨hEN,hNJ,?_⟩
  rw [he] at h32 hmod ⊢
  change 2^k % 3 = 8 % 3 at hmod
  interval_cases k <;> norm_num at *
/-- The order-32 alternative would put the fixed subgroup inside the
normal closure, forcing the whole five-root subgroup into that normalizer.
Consequently the normalizer is exactly the five-root subgroup. -/
theorem separated_binary_fixedOddRoots_normalizer
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (s : RootReflection Q split i)
    (hF : Nat.card F = 2)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (hc3 : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hCJ : middleRootCentralizer Q split i j = middleFive Q split i j) :
    simpleRemainder Q split i ⊓ normalizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D)) =
      middleFive Q split i j := by
  let V := simpleRemainder Q split i
  let M := fixedOddRoots Q split i j
  let J := middleFive Q split i j
  let N := V ⊓ normalizer (M : Set (X ⧸ Q.D))
  obtain ⟨hEN,hNJ,hcard⟩ := separated_binary_fixedOddRoots_normalizer_card Q split hm i j hij
    hKi hKj μi s hF hi hj c hc3 hc hCJ
  change middleRootClosure Q split i j ≤ N at hEN
  change N ≤ J at hNJ
  change Nat.card N = 32 ∨ Nat.card N = 128 at hcard
  have hJV : J ≤ V := middleFive_le_remainder Q split hm i j hij
  have hJC : J ≤ middleRootCentralizer Q split i j := hCJ.ge
  have hJcard : Nat.card J = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
  have hMJ : M ≤ J := sup_le
    (sup_le (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))) le_sup_right
  have hMN : M ≤ N := le_inf (hMJ.trans hJV) M.le_normalizer
  rcases hcard with h32 | h128
  · have hi16 : (middleRootCentralizer Q split i j).relIndex V = 16 := by
      rw [hCJ]
      exact binary_middleFive_quotient_card Q split hm i j hij hi hj
    have hbound := (binary_middleRootClosure_card_bounds Q split hm i j hij hKj hi hj hJC).2.2 hi16
    have he : middleRootClosure Q split i j = N := eq_of_le_of_card_ge hEN (by rwa [h32])
    have hEC := (middleRootClosure_le_middle_center Q split hm i j hij hKj hJC).trans inf_le_right
    have hMC : M ≤ centralizer (J : Set (X ⧸ Q.D)) := hMN.trans (he ▸ hEC)
    have hJN : J ≤ N := le_inf hJV ((le_centralizer_iff.mp hMC).trans
      (Subgroup.centralizer_le_normalizer _))
    have hh := card_le_of_le hJN
    rw [hJcard,h32] at hh
    omega
  · exact eq_of_le_of_card_ge hNJ (by rw [hJcard,h128])


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
