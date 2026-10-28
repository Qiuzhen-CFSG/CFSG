module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Checks

/-!
# Interpretation of staged cross-composition certificates

Every cross check is transported through already interpreted predecessor
words. Right multiplication is cancelled using the original permutation,
never an unverified numerical table. This proves the exact ten full-degree
word agreements from four independent finite-computation obligations.

Source: the literal stabilizer word formulas in `FirstFour.Words` and
`Transitions.WordModel`, ATLAS F24G1-p306936B0, GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
open Tables FirstFourModel

/-- Agreement on every original ambient letter. -/
def Agrees (p : Equiv.Perm (Fin 306936)) (f : Nat → Nat) : Prop :=
  ∀ x : Fin 306936, (p x).val = f x.val

/-- An inverse-free cross-composition check interprets a right quotient. -/
theorem agrees_mul_inv {p q : Equiv.Perm (Fin 306936)} {f l r : Nat → Nat}
    (hp : Agrees p l) (hq : Agrees q r) (h : Checks (crossTest f l r)) :
    Agrees (p * q⁻¹) f := by
  intro x
  have hc := h (q⁻¹ x)
  simp only [crossTest, Nat.mod_eq_of_lt (q⁻¹ x).isLt, beq_iff_eq] at hc
  rw [← hq (q⁻¹ x)] at hc
  have he : q (q⁻¹ x) = x := q.apply_symm_apply x
  rw [he] at hc
  exact (hp (q⁻¹ x)).trans hc.symm

/-- Compose agreements without comparing distinct nested word constants. -/
theorem agrees_mul {p q : Equiv.Perm (Fin 306936)} {f g : Nat → Nat}
    (hp : Agrees p f) (hq : Agrees q g) :
    Agrees (p * q) (fun x => f (g x)) := by
  intro x
  exact (hp (q x)).trans (congrArg f (hq x))

/-- A square check supplies the inverse action of the same genuine permutation. -/
theorem agrees_inv_of_square {p : Equiv.Perm (Fin 306936)} {f : Nat → Nat}
    (hp : Agrees p f) (h : ∀ x : Fin 306936, f (f x.val) = x.val) :
    Agrees p⁻¹ f := by
  intro x
  have hx := h (p⁻¹ x)
  rw [← hp (p⁻¹ x)] at hx
  have he : p (p⁻¹ x) = x := p.apply_symm_apply x
  rw [he] at hx
  exact hx.symm

theorem agrees5
    (h : Checks check5) :
    Agrees (FirstFourModel.Word.word5 aPerm bPerm) raw5 := by
  unfold FirstFourModel.Word.word5
  apply agrees_mul_inv (l := left5) (r := right5) ?_ ?_ h
  · intro x
    rfl
  · intro x
    rfl

theorem agrees8
    (h : Checks check8) :
    Agrees (FirstFourModel.Word.word8 aPerm bPerm) raw8 := by
  unfold FirstFourModel.Word.word8
  apply agrees_mul_inv (l := left8) (r := right8) ?_ ?_ h
  · intro x
    rfl
  · intro x
    rfl

theorem agrees11
    (h5 : Agrees (FirstFourModel.Word.word5 aPerm bPerm) raw5)
    (h8 : Agrees (FirstFourModel.Word.word8 aPerm bPerm) raw8)
    (h : Checks check11) :
    Agrees (FirstFourModel.Word.word11 aPerm bPerm) raw11 := by
  unfold FirstFourModel.Word.word11
  apply agrees_mul_inv (l := left11) (r := right11) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h8 h5) h5) h8) h8) h5) h8) h5) h5) h8) h5) h8) h5) h8) h5) h5)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h8 h5) h5) h5) h5) h5) h5) h5) h8) h8) h5) h8) h8) h5) h8)
    exact hh

theorem agrees14
    (h5 : Agrees (FirstFourModel.Word.word5 aPerm bPerm) raw5)
    (h8 : Agrees (FirstFourModel.Word.word8 aPerm bPerm) raw8)
    (h : Checks check14) :
    Agrees (FirstFourModel.Word.word14 aPerm bPerm) raw14 := by
  unfold FirstFourModel.Word.word14
  apply agrees_mul_inv (l := left14) (r := right14) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h8 h8) h5) h8) h5) h5) h5) h8) h8) h5) h5) h5) h8)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h5 h8) h8) h8) h8) h8) h5) h5) h8) h5) h8) h8) h5)
    exact hh

theorem agrees17
    (h11 : Agrees (FirstFourModel.Word.word11 aPerm bPerm) raw11)
    (h14 : Agrees (FirstFourModel.Word.word14 aPerm bPerm) raw14)
    (h : Checks check17) :
    Agrees (FirstFourModel.Word.word17 aPerm bPerm) raw17 := by
  unfold FirstFourModel.Word.word17
  apply agrees_mul_inv (l := left17) (r := right17) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h11 h14) h14) h14) h11) h11) h14) h11) h14) h14) h11) h11) h11) h11)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h11 h14) h11) h14) h14) h11) h14)
    exact hh

theorem agrees20
    (h11 : Agrees (FirstFourModel.Word.word11 aPerm bPerm) raw11)
    (h14 : Agrees (FirstFourModel.Word.word14 aPerm bPerm) raw14)
    (h : Checks check20) :
    Agrees (FirstFourModel.Word.word20 aPerm bPerm) raw20 := by
  unfold FirstFourModel.Word.word20
  apply agrees_mul_inv (l := left20) (r := right20) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h11 h14) h11) h14) h11) h11) h14) h11) h14) h14) h11) h11) h11)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h14 h14) h11) h14) h14) h14) h11) h14) h14) h14) h11) h14)
    exact hh

theorem agrees23
    (h17 : Agrees (FirstFourModel.Word.word17 aPerm bPerm) raw17)
    (h20 : Agrees (FirstFourModel.Word.word20 aPerm bPerm) raw20)
    (h : Checks check23) :
    Agrees (FirstFourModel.Word.word23 aPerm bPerm) raw23 := by
  unfold FirstFourModel.Word.word23
  apply agrees_mul_inv (l := left23) (r := right23) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h20 h20) h20) h20) h20) h20) h20) h17) h17) h17) h17)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h20) h20) h17) h20) h20) h20) h20) h17) h17) h20)
    exact hh

theorem agrees26
    (h17 : Agrees (FirstFourModel.Word.word17 aPerm bPerm) raw17)
    (h20 : Agrees (FirstFourModel.Word.word20 aPerm bPerm) raw20)
    (h : Checks check26) :
    Agrees (FirstFourModel.Word.word26 aPerm bPerm) raw26 := by
  unfold FirstFourModel.Word.word26
  apply agrees_mul_inv (l := left26) (r := right26) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h17) h17) h20) h20) h20) h17) h20) h20) h20) h17)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h20) h17) h17) h17) h20)
    exact hh

theorem agrees29
    (h17 : Agrees (FirstFourModel.Word.word17 aPerm bPerm) raw17)
    (h20 : Agrees (FirstFourModel.Word.word20 aPerm bPerm) raw20)
    (h : Checks check29) :
    Agrees (FirstFourModel.Word.word29 aPerm bPerm) raw29 := by
  unfold FirstFourModel.Word.word29
  apply agrees_mul_inv (l := left29) (r := right29) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h17) h17) h20) h17) h17) h20) h17) h20) h20)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h17) h20) h20) h17) h17) h20) h17) h17)
    exact hh

theorem agrees32
    (h17 : Agrees (FirstFourModel.Word.word17 aPerm bPerm) raw17)
    (h20 : Agrees (FirstFourModel.Word.word20 aPerm bPerm) raw20)
    (h : Checks check32) :
    Agrees (FirstFourModel.Word.word32 aPerm bPerm) raw32 := by
  unfold FirstFourModel.Word.word32
  apply agrees_mul_inv (l := left32) (r := right32) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h17 h20) h20) h17) h17) h20) h17) h20) h17) h17)
    exact hh
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul (agrees_mul h20 h17) h20) h17) h20) h20)
    exact hh

theorem agrees35
    (h23 : Agrees (FirstFourModel.Word.word23 aPerm bPerm) raw23)
    (h26 : Agrees (FirstFourModel.Word.word26 aPerm bPerm) raw26)
    (h32 : Agrees (FirstFourModel.Word.word32 aPerm bPerm) raw32)
    (hinv : Checks square32)
    (h : Checks check35) : Agrees (Word.word35 aPerm bPerm) raw35 := by
  have hi32 : Agrees (FirstFourModel.Word.word32 aPerm bPerm)⁻¹ raw32 :=
    agrees_inv_of_square h32 fun x => by
      have hx := hinv x
      simpa only [square32, Nat.mod_eq_of_lt x.isLt, beq_iff_eq] using hx
  unfold Word.word35
  apply agrees_mul_inv (l := left35) (r := right35) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul h23 hi32) h23) h26)
    exact hh
  · have hh := (agrees_mul (agrees_mul h23 h26) h23)
    exact hh

theorem agrees38
    (h23 : Agrees (FirstFourModel.Word.word23 aPerm bPerm) raw23)
    (h26 : Agrees (FirstFourModel.Word.word26 aPerm bPerm) raw26)
    (h29 : Agrees (FirstFourModel.Word.word29 aPerm bPerm) raw29)
    (h32 : Agrees (FirstFourModel.Word.word32 aPerm bPerm) raw32)
    (h : Checks check38) : Agrees (Word.word38 aPerm bPerm) raw38 := by
  simp only [Word.word38, Word.word36, Word.word37, mul_inv_rev, inv_inv]
  rw [← mul_assoc]
  apply agrees_mul_inv (l := left38) (r := right38) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul (agrees_mul (agrees_mul h23 h26) h23) h29) h32)
    exact hh
  · exact h23

theorem agrees41
    (h23 : Agrees (FirstFourModel.Word.word23 aPerm bPerm) raw23)
    (h26 : Agrees (FirstFourModel.Word.word26 aPerm bPerm) raw26)
    (h29 : Agrees (FirstFourModel.Word.word29 aPerm bPerm) raw29)
    (h : Checks check41) : Agrees (Word.word41 aPerm bPerm) raw41 := by
  unfold Word.word41
  apply agrees_mul_inv (l := left41) (r := right41) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul h26 h26) h26)
    exact hh
  · have hh := (agrees_mul (agrees_mul h26 h23) h29)
    exact hh

theorem agrees44
    (h35 : Agrees (Word.word35 aPerm bPerm) raw35)
    (h38 : Agrees (Word.word38 aPerm bPerm) raw38)
    (h41 : Agrees (Word.word41 aPerm bPerm) raw41)
    (h : Checks check44) : Agrees (Word.word44 aPerm bPerm) raw44 := by
  unfold Word.word44
  apply agrees_mul_inv (l := left44) (r := right44) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul h38 h41) h35)
    exact hh
  · have hh := (agrees_mul h41 h38)
    exact hh

theorem agrees47
    (h35 : Agrees (Word.word35 aPerm bPerm) raw35)
    (h38 : Agrees (Word.word38 aPerm bPerm) raw38)
    (h41 : Agrees (Word.word41 aPerm bPerm) raw41)
    (h : Checks check47) : Agrees (Word.word47 aPerm bPerm) raw47 := by
  unfold Word.word47
  apply agrees_mul_inv (l := left47) (r := right47) ?_ ?_ h
  · have hh := (agrees_mul (agrees_mul h41 h38) h41)
    exact hh
  · exact h35

theorem agrees50
    (h44 : Agrees (Word.word44 aPerm bPerm) raw44)
    (h47 : Agrees (Word.word47 aPerm bPerm) raw47)
    (h : Checks check50) : Agrees (Word.word50 aPerm bPerm) raw50 := by
  unfold Word.word50
  apply agrees_mul_inv (l := left50) (r := right50) ?_ ?_ h
  · have hh := (agrees_mul h47 h44)
    exact hh
  · exact h47

/-- All numerical premises are discharged by the four independent checker owners. -/
theorem tableAgreement_of_checks (hs : SeedChecks) (hm : MiddleChecks)
    (hf : FrontChecks) (ht : TailChecks) : TableAgreement := by
  obtain ⟨c5, c8⟩ := hs
  obtain ⟨c11, c14, c17, c20⟩ := hm
  obtain ⟨c23, c26, c29, c32⟩ := hf
  obtain ⟨c32inv, c35, c38, c41, c44, c47, c50⟩ := ht
  have h5 := agrees5 c5
  have h8 := agrees8 c8
  have h11 := agrees11 h5 h8 c11
  have h14 := agrees14 h5 h8 c14
  have h17 := agrees17 h11 h14 c17
  have h20 := agrees20 h11 h14 c20
  have h23 := agrees23 h17 h20 c23
  have h26 := agrees26 h17 h20 c26
  have h29 := agrees29 h17 h20 c29
  have h32 := agrees32 h17 h20 c32
  have h35 := agrees35 h23 h26 h32 c32inv c35
  have h38 := agrees38 h23 h26 h29 h32 c38
  have h41 := agrees41 h23 h26 h29 c41
  have h44 := agrees44 h35 h38 h41 c44
  have h47 := agrees47 h35 h38 h41 c47
  have h50 := agrees50 h44 h47 c50
  exact tableAgreement_of_word_checks h23 h26 h29 h32 h35 h38 h41 h44 h47 h50

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
