module
public import Theory.SpecificGroups.ReeTwo.FixingModelNonsplitStructure
public import Theory.SpecificGroups.ReeTwo.FixingModelReduction

/-!
# The fixed mark in the nonsplit base-action first core

In action 19, the last root has 768 fourth roots in the first core. Each of
the other two nonidentity central elements has only 256. Automorphisms preserve
these fiber cardinalities, so they fix the last root. The marked ambient
isomorphism from action 19 to action 0 transfers the conclusion.

The square polynomial is verified against collected multiplication and applied
twice to obtain the fourth-power polynomial. The resulting finite fiber counts
are checked by the kernel. The structure and counting argument adapt
`InvertingModelNonsplitZero`, with the fixing action checked separately.

Source: Shinoda (1975), pp.81–83, through `SylowCollectedArithmetic` and the
nonsplit carry construction; invariance of power fibers under isomorphisms.
-/

namespace ReeTwo.FixingModel.NonsplitZero

private def coordinateFourth (x : G) : G :=
  let s := coordinateMul x x
  coordinateMul s s

private theorem coordinateFourth_eq (x : G) : coordinateFourth x = x ^ 4 := by
  simp only [coordinateFourth, coordinateMul_eq_mul]
  simp only [show 4 = 2 * 2 from rfl, pow_mul, pow_two]

private def fourthPolynomial (p : Params) : G :=
  let x := (elt p).core
  if p.2.val = 0 then ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,0⟩
  else if p.2.val = 1 then ⟨⟨0, 0, 0, 0, 0, 0, 0, 0,
      x.b1*x.b2 + x.b1*x.b3 + x.b5,
      1 + x.b1*x.b2 + x.b1*x.b3 + x.b1*x.b5⟩,0⟩
  else if p.2.val = 2 then ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0,
      x.b1⟩,0⟩
  else ⟨⟨0, 0, 0, 0, 0, 0, 0, 0,
      x.b1 + x.b1*x.b2 + x.b1*x.b3 + x.b5,
      1 + x.b1 + x.b1*x.b2 + x.b1*x.b3 + x.b1*x.b5⟩,0⟩

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

private def squarePolynomial (g : G) : G :=
  let x := g.core
  if g.idx.val = 0 then ⟨⟨0, 0, 0, 0, 0,
      x.b1,
      x.b1*x.b2,
      x.b2*x.b3 + x.b1*x.b4,
      x.b3 + x.b1*x.b4 + x.b2*x.b4,
      x.b2 + x.b1*x.b4 + x.b4*x.b5 + x.b3*x.b6 + x.b1*x.b7⟩,0⟩
  else if g.idx.val = 1 then ⟨⟨0, 0,
      x.b1,
      x.b1,
      x.b1 + x.b3,
      x.b1,
      x.b1 + x.b1*x.b2 + x.b5,
      x.b1*x.b2 + x.b1*x.b3 + x.b2*x.b3 + x.b1*x.b4 + x.b6,
      x.b1 + x.b1*x.b2 + x.b3 + x.b2*x.b4 + x.b5 + x.b6 + x.b7,
      x.b2 + x.b1*x.b2 + x.b1*x.b4 + x.b5 + x.b1*x.b5 + x.b3*x.b5 + x.b4*x.b5 + x.b6 + x.b1*x.b6 +
        x.b3*x.b6 + x.b1*x.b7⟩,2⟩
  else if g.idx.val = 2 then ⟨⟨0, 0, 0, 0,
      x.b1,
      x.b1,
      x.b1*x.b2,
      x.b2*x.b3 + x.b1*x.b4 + x.b5,
      x.b1 + x.b1*x.b2 + x.b3 + x.b1*x.b4 + x.b2*x.b4 + x.b5 + x.b6,
      1 + x.b2 + x.b1*x.b4 + x.b5 + x.b1*x.b5 + x.b4*x.b5 + x.b3*x.b6 + x.b1*x.b7⟩,0⟩
  else ⟨⟨0, 0,
      x.b1,
      x.b1,
      x.b3,
      x.b1,
      x.b1 + x.b1*x.b2 + x.b5,
      x.b1*x.b2 + x.b1*x.b3 + x.b2*x.b3 + x.b1*x.b4 + x.b5 + x.b6,
      x.b3 + x.b2*x.b4 + x.b5 + x.b7,
      1 + x.b2 + x.b1*x.b2 + x.b1*x.b4 + x.b3*x.b5 + x.b4*x.b5 + x.b6 + x.b1*x.b6 + x.b3*x.b6 +
        x.b1*x.b7⟩,2⟩


set_option maxHeartbeats 8000000 in
private theorem squarePolynomial_eq (g : G) (hg : g.core.b0 = 0) :
    squarePolynomial g = coordinateMul g g := by
  obtain ⟨x,t⟩ := g
  change x.b0 = 0 at hg
  fin_cases t <;> apply CyclicFourCentralExtension.Model.ext
  all_goals first
    | apply Core.ext
    | rfl
    | apply Fin.ext; norm_num [squarePolynomial, coordinateMul]
  all_goals simp [squarePolynomial, coordinateMul, coordinateAction,
    action2, action3, SylowModel.Collected.actionPolynomial,
    core_mul_eq, Core.mul, Core.root, Core.ofCoords, hg]
  all_goals try ring_nf
  all_goals reduce_mod_char
  all_goals try simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
    show ∀ z : ZMod 2, z ^ 3 = z from by decide]
  all_goals try ring_nf
  all_goals reduce_mod_char

private theorem squarePolynomial_b0 (g : G) : (squarePolynomial g).core.b0 = 0 := by
  unfold squarePolynomial
  split_ifs <;> rfl

set_option maxHeartbeats 8000000 in
private theorem fourthPolynomial_eq (p : Params) : fourthPolynomial p = coordinateFourth (elt p) := by
  unfold coordinateFourth
  rw [← squarePolynomial_eq (elt p) rfl,
    ← squarePolynomial_eq _ (squarePolynomial_b0 _)]
  obtain ⟨b,t⟩ := p
  fin_cases t <;> apply CyclicFourCentralExtension.Model.ext
  all_goals first
    | apply Core.ext
    | rfl
  all_goals simp [fourthPolynomial, squarePolynomial, elt]
  all_goals try ring_nf
  all_goals reduce_mod_char
  all_goals try simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals try ring_nf
  all_goals reduce_mod_char

private def count (x : G) : ℕ := Fintype.card {p : Params // fourthPolynomial p = x}

private noncomputable def fourthRootCard (x : K) : ℕ := Nat.card {y : K // y ^ 4 = x}

private theorem fourthRootCard_aut (a : MulAut K) (x : K) :
    fourthRootCard (a x) = fourthRootCard x := by
  symm
  apply Nat.card_congr
  refine a.toEquiv.subtypeEquiv ?_
  intro y
  change y ^ 4 = x ↔ (a y) ^ 4 = a x
  rw [← map_pow, a.injective.eq_iff]

private theorem fourthRootCard_eq (x : K) : fourthRootCard x = count x.val := by
  unfold fourthRootCard count
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine parameterEquiv.subtypeEquiv ?_
  intro y
  rw [fourthPolynomial_eq, coordinateFourth_eq]
  have he : elt (parameterEquiv y) = y.val := congrArg Subtype.val (parameterEquiv.symm_apply_apply y)
  rw [he]
  exact Subtype.ext_iff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem counts : count (root 9) = 768 ∧ count (root 8) = 256 ∧
    count (root 8 * root 9) = 256 := by
  decide +kernel

/-- The marked element has exactly 768 fourth roots in the nonsplit first core. -/
public theorem marked_fourth_roots :
    Nat.card {y : K // y ^ 4 = centralInvolution 19 true} = 768 := by
  change fourthRootCard (centralInvolution 19 true) = 768
  rw [fourthRootCard_eq]
  exact counts.1

/-- Fourth-root counts distinguish the last root in the action-19 model. -/
public theorem nineteen_fixed (a : MulAut K) :
    a (centralInvolution 19 true) = centralInvolution 19 true := by
  have hc : a (centralInvolution 19 true) ∈ Subgroup.center K := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a
      (Subgroup.mem_center_iff.mp (centralInvolution_mem_center 19 true) x)
  have hn : a (centralInvolution 19 true) ≠ 1 := by
    intro h
    exact centralInvolution_ne_one 19 true (a.injective (h.trans (map_one a).symm))
  have hcount := fourthRootCard_aut a (centralInvolution 19 true)
  rw [fourthRootCard_eq, fourthRootCard_eq] at hcount
  change count (a (centralInvolution 19 true)).val = count (root 9) at hcount
  rcases K_center_cases _ hc with h | h | h | h
  · exact False.elim (hn (Subtype.ext h))
  · rw [h, counts.1, counts.2.1] at hcount
    omega
  · exact Subtype.ext h
  · rw [h, counts.1, counts.2.2] at hcount
    omega

end ReeTwo.FixingModel.NonsplitZero

namespace ReeTwo.FixingModel

/-- Every automorphism of the nonsplit base-action first core fixes the mark. -/
public theorem zero_true_fixed (a : MulAut (firstCore 0 true)) :
    a (centralInvolution 0 true) = centralInvolution 0 true := by
  obtain ⟨e, he⟩ := exists_marked_base_equiv 19 true
  change Model 19 true ≃* Model 0 true at e
  change e (mark 19 true) = mark 0 true at he
  apply fixed_of_marked_equiv e.symm _ NonsplitZero.nineteen_fixed a
  rw [← he, e.symm_apply_apply]

end ReeTwo.FixingModel
