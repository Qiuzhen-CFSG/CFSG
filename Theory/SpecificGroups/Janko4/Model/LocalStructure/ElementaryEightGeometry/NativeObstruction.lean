module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftRelations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.FiniteObstruction

/-!
# The native signed-pair obstruction for the two (b) images

Unique kernel coordinates convert involutivity and commutation of arbitrary
lifts into finite linear equations. Six selected bits give a contradiction
for both the primed and unprimed (b) quotient images with the specified signed
pair lift. The statement keeps that native marking explicit; transporting all
source Case (iii) occurrences to this marking is a further obligation.
Source: Kleidman--Wilson (1988), Proposition 2.3.4(ii), printed p.492.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

private theorem mask_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : nativeMask m = nativeMask n) : m = n := by
  have he : e ⟨m,hm⟩ = e ⟨n,hn⟩ := Subtype.ext h
  exact congrArg Fin.val ((e).injective he)

private theorem shifted_square (i : Fin 6) (m : Fin 2048)
    (hs : (nativeMask m.val * correctedLift i) * (nativeMask m.val * correctedLift i) = 1) :
    starMask (starElement i) m.val = m.val := by
  have he : nativeMask m.val * nativeMask (starMask (starElement i) m.val) = 1 := by
    calc
      _ = (nativeMask m.val * correctedLift i) * (nativeMask m.val * correctedLift i) := by
        calc
          _ = nativeMask m.val * (nativeMask (starMask (starElement i) m.val) * correctedLift i) * correctedLift i := by
            simp only [mul_assoc, correctedLift_square, mul_one]
          _ = nativeMask m.val * (correctedLift i * nativeMask m.val) * correctedLift i := by
            rw [correctedLift_mask_mul]
          _ = _ := by simp only [mul_assoc]
      _ = 1 := hs
  exact mask_injective (starMask_lt _ _) m.isLt
    (mul_left_cancel (he.trans (nativeMask_square m.val).symm))

private theorem shifted_commute (i j : Fin 6) (m n : Fin 2048)
    (hij : Commute (correctedLift i) (correctedLift j))
    (h : Commute (nativeMask m.val * correctedLift i) (nativeMask n.val * correctedLift j)) :
    starMask (starElement i) n.val ^^^ n.val = starMask (starElement j) m.val ^^^ m.val := by
  have eqmul (k h l t a : L) (ha : l * h = a * l) :
      (k * l) * (h * t) = (k * a) * (l * t) := by
    calc
      _ = k * (l * h) * t := by simp only [mul_assoc]
      _ = k * (a * l) * t := by rw [ha]
      _ = _ := by simp only [mul_assoc]
  have hh := h.eq
  rw [eqmul _ _ _ _ _ (correctedLift_mask_mul i n),
      eqmul _ _ _ _ _ (correctedLift_mask_mul j m), hij.eq] at hh
  have hmasks := mul_right_cancel hh
  rw [← nativeMask_xor, ← nativeMask_xor] at hmasks
  have hnum : m.val ^^^ starMask (starElement i) n.val =
      n.val ^^^ starMask (starElement j) m.val :=
    mask_injective (Nat.xor_lt_two_pow (n := 11) m.isLt (starMask_lt _ _))
      (Nat.xor_lt_two_pow (n := 11) n.isLt (starMask_lt _ _)) hmasks
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := congrArg (fun a : ℕ => a.testBit k) hnum
  simp only [Nat.testBit_xor] at hk ⊢
  revert hk
  cases m.val.testBit k <;> cases n.val.testBit k <;>
    cases (starMask (starElement i) n.val).testBit k <;>
    cases (starMask (starElement j) m.val).testBit k <;> decide

/-- The second marked pair lift with the specified native kernel sign change. -/
def twistedPairLift : L := nativeMask 4 * correctedLift 5

/-- Literal lift obstruction: the two primed-(b) quotient generators cannot
 lift to commuting involutions centralizing this marked pair element. -/
theorem no_twistedPair_b_lifts (x y : L)
    (hx : π x = starElement 1) (hy : π y = starElement 2)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : Commute x y)
    (hyp : Commute y twistedPairLift) : False := by
  obtain ⟨m,rfl,_⟩ := (correctedLift_fibre 1 x).mp hx
  obtain ⟨n,rfl,_⟩ := (correctedLift_fibre 2 y).mp hy
  have h1 := shifted_square 1 m hx2
  have h2 := shifted_square 2 n hy2
  have h12 : Commute (correctedLift 1) (correctedLift 2) := correctedGenerator_commute 0 1 2
  have h25 : Commute (correctedLift 2) (correctedLift 5) := correctedGenerator_commute 0 2 3
  have hc := (shifted_commute 1 2 m n h12 hxy).symm
  have hp := (shifted_commute 2 5 n 4 h25 hyp).symm
  have ha1 (a : ℕ) : starMask (starElement 1) a = maskImage (actionRows 0 1) a :=
    rowGenerator_mask 0 1 a
  have ha2 (a : ℕ) : starMask (starElement 2) a = maskImage (actionRows 0 2) a :=
    rowGenerator_mask 0 2 a
  have ha5 (a : ℕ) : starMask (starElement 5) a = maskImage pairActionRows a :=
    pairPermutation_mask a
  simp only [ha1,ha2] at h1 h2 hc
  simp only [ha2,ha5] at hp
  have h4 : maskImage (actionRows 0 2) 4 ^^^ 4 = 1129 := by decide +kernel
  have hp' : maskImage pairActionRows n.val ^^^ n.val = 1129 := hp.trans h4
  exact no_bbb_pair_masks m n h1 h2 hp' hc

/-- The obstruction applies to an arbitrary elementary subgroup with the
 actual quotient generators and the actual marked lift. -/
theorem elementary_image_excludes_b (A : Subgroup L) [IsElementaryAbelian 2 A]
    (hp : twistedPairLift ∈ A)
    (h1 : starElement 1 ∈ A.map π) (h2 : starElement 2 ∈ A.map π) : False := by
  obtain ⟨x,hx,hxp⟩ := h1
  obtain ⟨y,hy,hyp⟩ := h2
  have comm (a b : L) (ha : a ∈ A) (hb : b ∈ A) : Commute a b :=
    congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) (⟨b,hb⟩ : A))
  apply no_twistedPair_b_lifts x y hxp hyp
  · simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  · simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  · exact comm x y hx hy
  · exact comm y twistedPairLift hy hp

/-- Both selected (b) images, unprimed and primed, are impossible with the
 fixed native signed-pair marking. -/
theorem elementary_image_ne_b_rows (A : Subgroup L) [IsElementaryAbelian 2 A]
    (hp : twistedPairLift ∈ A) (r : Fin 4) (hr : r = 0 ∨ r = 2)
    (hrow : A.map π = pairRowImage r) : False := by
  apply elementary_image_excludes_b A hp
  · rw [hrow]
    rcases hr with rfl | rfl
    · exact pairRowGenerator_mem 0 1
    · exact pairRowGenerator_mem 2 1
  · rw [hrow]
    rcases hr with rfl | rfl
    · exact pairRowGenerator_mem 0 2
    · exact pairRowGenerator_mem 2 2

end Janko4.LocalStructure.ElementaryEightGeometry
