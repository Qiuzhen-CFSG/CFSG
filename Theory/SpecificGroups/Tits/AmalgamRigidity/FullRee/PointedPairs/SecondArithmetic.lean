module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondAction

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial arithmetic for the second binary Ree reflection

The verified Weyl word is collected into four short root blocks.  Only its two
binary power coordinates and its cyclic-four coordinate require a finite split;
the seven remaining coordinates are polynomial identities.  These formulas are
used to classify the involutions in a fixed reflection fiber without reducing
the ambient matrix group or the full ordered radical word repeatedly.

Source: the verified second Weyl relations, in the conventions of Shinoda
(1975), pp. 81–83 and Parrott (1972), p. 683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension
open SylowModel.Collected

def secondWeylPolynomial (x : SylowModel) : SylowModel :=
  let u : ZMod 2 := x.right.toAdd.val
  let v : ZMod 2 := (x.right.toAdd.val / 2 : Nat)
  ⟨⟨0,
    u,
    x.left.b3 + x.left.b1*u,
    x.left.b2 + x.left.b1*u,
    x.left.b1*x.left.b2 + x.left.b6 + x.left.b5*u,
    u+v,
    x.left.b4 + x.left.b3*u + x.left.b1*v,
    x.left.b2*x.left.b3 + x.left.b1*x.left.b4 + x.left.b7 + x.left.b1*u +
      x.left.b5*u + x.left.b6*u + x.left.b1*v + x.left.b5*v,
    x.left.b1*x.left.b2*x.left.b3 + x.left.b1*x.left.b7 + x.left.b9 + x.left.b1*u +
      x.left.b1*x.left.b2*u + x.left.b1*x.left.b5*u + x.left.b6*u +
      x.left.b1*x.left.b6*u + x.left.b1*v + x.left.b5*v + x.left.b1*x.left.b5*v,
    x.left.b1*x.left.b4 + x.left.b8 + x.left.b1*x.left.b2*u + x.left.b6*u +
      x.left.b7*u + x.left.b5*v⟩,
    Multiplicative.ofAdd (-(x.left.b1.val : ZMod 4) + 2*(x.left.b5.val : ZMod 4))⟩

private def threeRoots (c d e : ZMod 2) : Core := ⟨0,0,d,c,0,0,e,c*d,0,0⟩
private def fourRoots (g h i j : ZMod 2) : Core := ⟨0,0,0,0,g,0,0,h,j,i⟩

private theorem threeRoots_word (c d e : ZMod 2) :
    Core.root 3^c.val * Core.root 2^d.val * Core.root 6^e.val = threeRoots c d e := by
  simp only [Core.root_pow]
  change Core.mul (Core.mul _ _) _ = _
  apply Core.ext <;> simp [Core.mul,Core.ofCoords,threeRoots]

private theorem fourRoots_word (g h i j : ZMod 2) :
    Core.root 4^g.val * Core.root 7^h.val * Core.root 9^i.val * Core.root 8^j.val = fourRoots g h i j := by
  simp only [Core.root_pow]
  change Core.mul (Core.mul (Core.mul _ _) _) _ = _
  apply Core.ext <;> simp [Core.mul,Core.ofCoords,fourRoots]

private def weylGrouped (b c d e f g h i j : ZMod 2) (t : ZMod 4) : SylowModel :=
  SemidirectProduct.inr ((FiveFour.generator 4)⁻¹^b.val) *
  SemidirectProduct.inl (threeRoots c d e) *
  SemidirectProduct.inr ((FiveFour.generator 4)⁻¹^(2*f.val)) *
  SemidirectProduct.inl (fourRoots g h i j) *
  SemidirectProduct.inl ⟨0,(t.val : ZMod 2),0,0,0,
    (t.val : ZMod 2)+(t.val/2 : Nat),0,0,0,0⟩

private theorem secondWeyl_word_grouped (b c d e f g h i j : ZMod 2) (t : ZMod 4) :
    radicalWord weylImage (⟨⟨0,b,c,d,e,f,g,h,i,j⟩, Multiplicative.ofAdd t⟩ : SylowModel) =
      weylGrouped b c d e f g h i j t := by
  have h0 : weylImage 0 = SylowModel.root 1 := rfl
  have h1 : weylImage 1 = SylowModel.rootOne := rfl
  have h2 : weylImage 2 = SylowModel.root 3 := rfl
  have h3 : weylImage 3 = SylowModel.root 2 := rfl
  have h4 : weylImage 4 = SylowModel.root 6 := rfl
  have h5 : weylImage 5 = SylowModel.rootOne^2 := rfl
  have h6 : weylImage 6 = SylowModel.root 4 := rfl
  have h7 : weylImage 7 = SylowModel.root 7 := rfl
  have h8 : weylImage 8 = SylowModel.root 9 := rfl
  have h9 : weylImage 9 = SylowModel.root 8 := rfl
  dsimp only [radicalWord]
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  have hgroup : SylowModel.rootOne^b.val * SylowModel.root 3^c.val * SylowModel.root 2^d.val *
    SylowModel.root 6^e.val * (SylowModel.rootOne^2)^f.val * SylowModel.root 4^g.val *
    SylowModel.root 7^h.val * SylowModel.root 9^i.val * SylowModel.root 8^j.val =
    SylowModel.rootOne^b.val * SemidirectProduct.inl (threeRoots c d e) *
    (SylowModel.rootOne^2)^f.val * SemidirectProduct.inl (fourRoots g h i j) := by
    rw [← threeRoots_word, ← fourRoots_word, map_mul, map_mul, map_mul, map_mul,
      map_mul, map_pow, map_pow, map_pow, map_pow, map_pow, map_pow, map_pow]
    simp only [SylowModel.root, mul_assoc]
  rw [hgroup]
  have hu (n : Nat) : SylowModel.rootOne^n =
      (SemidirectProduct.inr ((FiveFour.generator 4)⁻¹^n) : SylowModel) := (map_pow _ _ _).symm
  have hz (t : ZMod 4) : (SylowModel.root 1)⁻¹^t.val =
      (SemidirectProduct.inl ⟨0,(t.val : ZMod 2),0,0,0,
        (t.val : ZMod 2)+(t.val/2 : Nat),0,0,0,0⟩ : SylowModel) := by
    exact (by decide +kernel : ∀ t : ZMod 4, (SylowModel.root 1)⁻¹^t.val =
      (SemidirectProduct.inl ⟨0,(t.val : ZMod 2),0,0,0,
        (t.val : ZMod 2)+(t.val/2 : Nat),0,0,0,0⟩ : SylowModel)) t
  rw [hz, ← pow_mul, hu, hu]
  rfl

private theorem coreMul_eq (x y : Core) : x*y = Core.mul x y := rfl
private theorem coreOne_eq : (1 : Core) = ⟨0,0,0,0,0,0,0,0,0,0⟩ := rfl

private theorem three_action1 (c d e : ZMod 2) : actionPolynomial (threeRoots c d e) = ⟨0,0,d,c,c,0,e,c*d+e,c*d+e,e⟩ := (by decide +kernel : ∀ c d e : ZMod 2, actionPolynomial (threeRoots c d e) = ⟨0,0,d,c,c,0,e,c*d+e,c*d+e,e⟩) c d e
private theorem three_action2 (c d e : ZMod 2) : actionPolynomial (actionPolynomial (threeRoots c d e)) = ⟨0,0,d,c,0,0,e,c*d,e,0⟩ := (by decide +kernel : ∀ c d e : ZMod 2, actionPolynomial (actionPolynomial (threeRoots c d e)) = ⟨0,0,d,c,0,0,e,c*d,e,0⟩) c d e
private theorem three_action3 (c d e : ZMod 2) : actionPolynomial (actionPolynomial (actionPolynomial (threeRoots c d e))) = ⟨0,0,d,c,c,0,e,c*d+e,c*d,e⟩ := (by decide +kernel : ∀ c d e : ZMod 2, actionPolynomial (actionPolynomial (actionPolynomial (threeRoots c d e))) = ⟨0,0,d,c,c,0,e,c*d+e,c*d,e⟩) c d e
private theorem four_action1 (g h i j : ZMod 2) : actionPolynomial (fourRoots g h i j) = ⟨0,0,0,0,g,0,0,h,h+j,i⟩ := (by decide +kernel : ∀ g h i j : ZMod 2, actionPolynomial (fourRoots g h i j) = ⟨0,0,0,0,g,0,0,h,h+j,i⟩) g h i j
private theorem four_action2 (g h i j : ZMod 2) : actionPolynomial (actionPolynomial (fourRoots g h i j)) = ⟨0,0,0,0,g,0,0,h,j,i⟩ := (by decide +kernel : ∀ g h i j : ZMod 2, actionPolynomial (actionPolynomial (fourRoots g h i j)) = ⟨0,0,0,0,g,0,0,h,j,i⟩) g h i j
private theorem four_action3 (g h i j : ZMod 2) : actionPolynomial (actionPolynomial (actionPolynomial (fourRoots g h i j))) = ⟨0,0,0,0,g,0,0,h,h+j,i⟩ := (by decide +kernel : ∀ g h i j : ZMod 2, actionPolynomial (actionPolynomial (actionPolynomial (fourRoots g h i j))) = ⟨0,0,0,0,g,0,0,h,h+j,i⟩) g h i j
private theorem action_one : actionPolynomial (1:Core) = 1 := by decide +kernel

private theorem weylGrouped_eq_000 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 0 g h i j 0 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 0⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_001 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 0 g h i j 1 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 1⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_002 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 0 g h i j 2 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 2⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_003 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 0 g h i j 3 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 3⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_010 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 1 g h i j 0 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 0⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_011 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 1 g h i j 1 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 1⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_012 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 1 g h i j 2 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 2⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_013 (c d e g h i j : ZMod 2) :
    weylGrouped 0 c d e 1 g h i j 3 =
      secondWeylPolynomial (⟨⟨0,0,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 3⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_100 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 0 g h i j 0 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 0⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_101 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 0 g h i j 1 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 1⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_102 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 0 g h i j 2 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 2⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_103 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 0 g h i j 3 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,0,g,h,i,j⟩,Multiplicative.ofAdd 3⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_110 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 1 g h i j 0 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 0⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_111 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 1 g h i j 1 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 1⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_112 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 1 g h i j 2 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 2⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem weylGrouped_eq_113 (c d e g h i j : ZMod 2) :
    weylGrouped 1 c d e 1 g h i j 3 =
      secondWeylPolynomial (⟨⟨0,1,c,d,e,1,g,h,i,j⟩,Multiplicative.ofAdd 3⟩ : SylowModel) := by
  dsimp only [weylGrouped]
  all_goals simp only [ZMod.val_zero,show (1 : ZMod 4).val=1 from rfl, ZMod.val_one,pow_zero,pow_one,one_mul,mul_one]
  all_goals simp only [← collectedMul_eq]
  all_goals apply SemidirectProduct.ext
  all_goals first
    | rfl
    | (simp only [collectedMul,cyclicAction,Function.iterate_succ_apply,Function.iterate_zero_apply,
      secondWeylPolynomial,SylowModel.rootOne,SylowModel.root,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.mul_right,SemidirectProduct.inv_right])
  all_goals norm_num [FiveFour.generator, toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_pow, ZMod.val_natCast, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try simp only [show (-3 : ZMod 4)=1 from rfl, show (-2 : ZMod 4)=2 from rfl, show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_ofNat, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [three_action3]
  all_goals try rw [three_action2]
  all_goals try rw [three_action1]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try simp only [action_one]
  all_goals try exact (by decide +kernel)
  all_goals norm_num [show (1 : ZMod 4).val=1 from rfl, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast, ZMod.val_ofNat, toAdd_ofAdd, Function.iterate_succ_apply, Function.iterate_zero_apply]
  all_goals try rw [four_action3]
  all_goals try rw [four_action2]
  all_goals try rw [four_action1]
  all_goals try (apply Core.ext)
  all_goals try simp [coreMul_eq, coreOne_eq, Core.mul,Core.ofCoords, actionPolynomial,threeRoots,fourRoots]
  all_goals try simp [coreMul_eq,coreOne_eq,Core.mul,actionPolynomial]
  all_goals try ring_nf
  all_goals reduce_mod_char


theorem secondWeylPolynomial_word (b c d e f g h i j : ZMod 2) (t : ZMod 4) :
    radicalWord weylImage (⟨⟨0,b,c,d,e,f,g,h,i,j⟩, Multiplicative.ofAdd t⟩ : SylowModel) =
      secondWeylPolynomial (⟨⟨0,b,c,d,e,f,g,h,i,j⟩,Multiplicative.ofAdd t⟩ : SylowModel) := by
  rw [secondWeyl_word_grouped]
  fin_cases b <;> fin_cases f <;> fin_cases t
  · exact weylGrouped_eq_000 c d e g h i j
  · exact weylGrouped_eq_001 c d e g h i j
  · exact weylGrouped_eq_002 c d e g h i j
  · exact weylGrouped_eq_003 c d e g h i j
  · exact weylGrouped_eq_010 c d e g h i j
  · exact weylGrouped_eq_011 c d e g h i j
  · exact weylGrouped_eq_012 c d e g h i j
  · exact weylGrouped_eq_013 c d e g h i j
  · exact weylGrouped_eq_100 c d e g h i j
  · exact weylGrouped_eq_101 c d e g h i j
  · exact weylGrouped_eq_102 c d e g h i j
  · exact weylGrouped_eq_103 c d e g h i j
  · exact weylGrouped_eq_110 c d e g h i j
  · exact weylGrouped_eq_111 c d e g h i j
  · exact weylGrouped_eq_112 c d e g h i j
  · exact weylGrouped_eq_113 c d e g h i j

theorem secondWeylPolynomial_eq (x : radical) :
    secondWeylPolynomial x = (secondWeyl x).val := by
  rcases x with ⟨⟨⟨a,b,c,d,e,f,g,h,i,j⟩,t⟩,hx⟩
  change a = 0 at hx
  subst a
  exact (secondWeylPolynomial_word b c d e f g h i j t.toAdd).symm

end Tits.AmalgamRigidity.FullRee.PointedPairs
