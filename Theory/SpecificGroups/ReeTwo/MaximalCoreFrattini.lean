module

public import Theory.SpecificGroups.ReeTwo.MaximalCoreCoordinates
public import Theory.Frattini.PGroup

/-!
# Frattini containment for the four core-character kernels

The kernel of parity and the root-3 character on each `maximalCore a b`
is contained in its Frattini subgroup. Nine elements suffice: the square
of root 1, the two middle root pairs, and the last six core roots.
For each of the four parameter pairs, explicit words in the two corrected
root lifts express these elements. Every word has trivial image in the
binary rank-two group, hence in the elementary abelian Frattini quotient.

The image of the Frattini subgroup is normal in the ambient Sylow group.
The core normal form then shows that killing the nine elements kills every
element with all three binary characters trivial.

Source: Shinoda (1975), (2.3), pp. 81–83, via the verified root coordinates
in `Core`, `RootAction`, and `MaximalCoreCoordinates`. The explicit words
were found by a GAP search; their values and binary images are checked here
by Lean's kernel, independently of that search.
-/

namespace ReeTwo.SylowModel

private def evalWord {G : Type*} [Group G] (x y : G) (w : List ℤ) : G :=
  (w.map fun n => if n = 1 then x else if n = -1 then x⁻¹
    else if n = 2 then y else y⁻¹).prod

private theorem map_evalWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G) (w : List ℤ) :
    f (evalWord x y w) = evalWord (f x) (f y) w := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [Function.comp_apply]
  split_ifs <;> first | rfl | apply map_inv

-- Letters ±1 and ±2 denote the two lifts and their inverses.
private def coreWord (a b : ZMod 2) (i : Fin 9) : List ℤ :=
  if a = 0 then
    if b = 0 then ![[ 1, 1 ],
      [ 1, 1, 2, -1, 2, -1, 2, -1, 2, 1, 1, 2, -1, 2 ],
      [ 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2 ],
      [ 1, 2, 1, 2, 1, 2, -1, 2, -1, 2, 1, 2, -1, 2, -1, 2 ],
      [ 1, 1, 2, 1, 1, 2, 1, 1, 2, -1, 2, -1, 2, 1, 2, -1 ],
      [ 1, 1, 2, -1, 2, -1, 2, 1, 1, 2, -1, 2, -1, 2 ],
      [ 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, -1 ],
      [ 1, 1, 2, -1, 2, 1, 2, 1, 2, 1, 1, 2, -1, 2, -1, 2, 1, 2 ],
      [ 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2 ]] i
    else ![[ 1, 1 ],
      [ -1, -2, 1, -2, -1, 2, 2, 1 ],
      [ 1, 1, 2, 1, 1, 2 ],
      [ 1, -2, 1, 1, -2, -1, 2, 1, 1, 2 ],
      [ 2, 2 ],
      [ -1, 2, 1, 2, -1, -2, 1, 2 ],
      [ 1, 2, 2, -1, 2, -1, 2, 2, 1, -2 ],
      [ 1, 2, -1, -2, 1, -2, -1, -2 ],
      [ 1, 2, -1, 2, 2, 1, -2, -1, 2, 2 ]] i
  else if b = 0 then ![[ 1, 2, -1, 2, -1, -1, 2, -1, 2, 1 ],
      [ 2, -1, -1, 2, 1, 1, 2, -1, 2, 1 ],
      [ 2, -1, 2, 1, 2, 1, 2, -1 ],
      [ 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2 ],
      [ 1, 1, 2, 1, 2, -1, 2, 1, 2, 1 ],
      [ 1, 2, 1, 1, 2, 1, 2, -1, 2, -1, -1, 2, -1, 2 ],
      [ 1, 1, 2, 1, 1, 2, -1, -1, 2, -1, -1, 2 ],
      [ 2, 1, 1, 1, 1, 2 ],
      [ 1, 1, 1, 1, 2, 1, 1, 1, 1, 2 ]] i
  else ![[ 1, 2, 1, 1, 2, -1, 2, 2 ],
      [ -2, -1, -2, -1, -1, -1 ],
      [ 1, 1, 2, 1, 2, 2, 1, -2 ],
      [ -1, -2, -1, -2, -1, -2, -1, 2 ],
      [ 2, 2 ],
      [ 1, 1, 1, 2, 2, 1, 2, 2 ],
      [ 2, 1, 1, 2, 2, 1, 1, 2 ],
      [ 2, 1, 1, 1, 1, -2 ],
      [ 1, 1, 1, 1, 2, 1, 1, 1, 1, -2 ]] i

private def coreTarget (i : Fin 9) : SylowModel :=
  ![rootOne ^ 2, root 1 * root 3, root 2 * root 3,
    root 4, root 5, root 6, root 7, root 8, root 9] i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem coreWord_value : ∀ (a b : ZMod 2) (i : Fin 9),
    evalWord (rootOne * root 1 ^ a.val) (root 0 * root 1 ^ b.val) (coreWord a b i) =
      coreTarget i := by decide +kernel

private theorem coreWord_even : ∀ (a b : ZMod 2) (i : Fin 9),
    evalWord (FiveFour.generator 2, (1 : FiveFour.Cyclic 2))
      ((1 : FiveFour.Cyclic 2), FiveFour.generator 2) (coreWord a b i) = 1 := by
  decide +kernel

open scoped IsMulCommutative in
private theorem evenWord_mem_frattini {G : Type*} [Group G] [Finite G]
    [Fact (IsPGroup 2 G)] (x y : G) (w : List ℤ)
    (hw : evalWord (FiveFour.generator 2, (1 : FiveFour.Cyclic 2))
      ((1 : FiveFour.Cyclic 2), FiveFour.generator 2) w = 1) :
    evalWord x y w ∈ frattini G := by
  let Q := G ⧸ frattini G
  let _ : IsElementaryAbelian 2 Q := isElementaryAbelian_quotient_frattini (p := 2)
  let q := QuotientGroup.mk' (frattini G)
  have hs (z : Q) : z ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 Q) z
  let f := (FiveFour.cyclicHom (q x) (hs (q x))).coprod
    (FiveFour.cyclicHom (q y) (hs (q y)))
  apply (QuotientGroup.eq_one_iff _).mp
  change q (evalWord x y w) = 1
  calc
    _ = evalWord (q x) (q y) w := map_evalWord q x y w
    _ = f (evalWord (FiveFour.generator 2, (1 : FiveFour.Cyclic 2))
        ((1 : FiveFour.Cyclic 2), FiveFour.generator 2) w) := by
      rw [map_evalWord]
      simp only [f, MonoidHom.coprod_apply, FiveFour.cyclicHom_generator,
        map_one, mul_one, one_mul]
    _ = 1 := by rw [hw, map_one]

private theorem coreTarget_mem (a b : ZMod 2) (i : Fin 9) :
    coreTarget i ∈ (frattini (maximalCore a b)).map (maximalCore a b).subtype := by
  let _ : Fact (IsPGroup 2 (maximalCore a b)) := ⟨maximalCore_isPGroup a b⟩
  refine ⟨evalWord (maximalCoreFirst a b) (maximalCoreSecond a b) (coreWord a b i),
    evenWord_mem_frattini _ _ _ (coreWord_even a b i), ?_⟩
  exact (map_evalWord (maximalCore a b).subtype _ _ _).trans (coreWord_value a b i)

private theorem coordinate_kernel_le (W : Subgroup SylowModel) [W.Normal]
    (hW : ∀ i, coreTarget i ∈ W) (x : SylowModel)
    (hp : character x = 1) (hr : rootThreeCharacter x = 1)
    (hc : coreCharacter x = 1) : x ∈ W := by
  let q := QuotientGroup.mk' W
  have ht (i : Fin 9) : q (coreTarget i) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hW i)
  have htail (i : CoreRoot) (hi : 4 ≤ i.val) : q (root i) = 1 := by
    fin_cases i <;> norm_num at hi
    all_goals first
      | exact ht 3
      | exact ht 4
      | exact ht 5
      | exact ht 6
      | exact ht 7
      | exact ht 8
  have h13 : q (root 1) * q (root 3) = 1 := by
    rw [← map_mul]; exact ht 1
  have h23 : q (root 2) * q (root 3) = 1 := by
    rw [← map_mul]; exact ht 2
  have h33 : q (root 3) * q (root 3) = 1 := by
    rw [← map_mul, show root 3 * root 3 = root 8 from by decide +kernel]
    exact htail 8 (by decide)
  have h1 : q (root 1) = q (root 3) := mul_right_cancel (h13.trans h33.symm)
  have h2 : q (root 2) = q (root 3) := mul_right_cancel (h23.trans h33.symm)
  have h0 : x.left.b0 = 0 := congrArg Multiplicative.toAdd hr
  have hsum : x.left.b1 + x.left.b2 + x.left.b3 = 0 :=
    congrArg Multiplicative.toAdd hc
  have hb : ∀ a b c : ZMod 2, a + b + c = 0 →
      q (root 3) ^ a.val * q (root 3) ^ b.val * q (root 3) ^ c.val = 1 := by
    intro a b c
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a with rfl | rfl <;>
      rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) b with rfl | rfl <;>
      rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) c with rfl | rfl <;>
      simp only [show (0 : ZMod 2).val = 0 from rfl,
        show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one,
        one_mul, mul_one, h33]
    all_goals first | trivial | intro h; exact absurd h (by decide)
  have hl : q (SemidirectProduct.inl x.left) = 1 := by
    have hn := congrArg (q.comp (SemidirectProduct.inl : Core →* SylowModel))
      (Core.normal_form x.left)
    simp only [map_mul, map_pow, MonoidHom.comp_apply] at hn
    change q (root 0) ^ x.left.b0.val * q (root 1) ^ x.left.b1.val *
      q (root 2) ^ x.left.b2.val * q (root 3) ^ x.left.b3.val *
      q (root 4) ^ x.left.b4.val * q (root 5) ^ x.left.b5.val *
      q (root 6) ^ x.left.b6.val * q (root 7) ^ x.left.b7.val *
      q (root 8) ^ x.left.b8.val * q (root 9) ^ x.left.b9.val = _ at hn
    simp only [h0, show (0 : ZMod 2).val = 0 from rfl, pow_zero, one_mul,
      htail 4 (by decide), htail 5 (by decide), htail 6 (by decide),
      htail 7 (by decide), htail 8 (by decide), htail 9 (by decide),
      one_pow, mul_one, h1, h2] at hn
    exact hn.symm.trans (hb _ _ _ hsum)
  have he : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
      (SemidirectProduct.inr t : SylowModel) = 1 ∨
      (SemidirectProduct.inr t : SylowModel) = rootOne ^ 2 := by decide +kernel
  have hr' : q (SemidirectProduct.inr x.right) = 1 := by
    rcases he x.right hp with h | h
    · rw [h, map_one]
    · rw [h]; exact ht 0
  apply (QuotientGroup.eq_one_iff _).mp
  change q x = 1
  have heq : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
  rw [heq]
  rw [map_mul, hl, hr', one_mul]

/-- The common coordinate kernel is contained in each core kernel's Frattini subgroup. -/
public theorem maximalCoreQuotient_ker_le_frattini (a b : ZMod 2) :
    (maximalCoreQuotient a b).ker ≤ frattini (maximalCore a b) := by
  intro x hx
  have hp : character (x : SylowModel) = 1 := congrArg Prod.fst hx
  have hr : rootThreeCharacter (x : SylowModel) = 1 := congrArg Prod.snd hx
  have hc : coreCharacter (x : SylowModel) = 1 := by
    have hm := x.property
    change (maximalCharacter a b 1) (x : SylowModel) = 1 at hm
    simpa [maximalCharacter, hp, hr, show (1 : ZMod 2).val = 1 from rfl] using hm
  have hw := coordinate_kernel_le
    ((frattini (maximalCore a b)).map (maximalCore a b).subtype)
    (coreTarget_mem a b) x hp hr hc
  obtain ⟨y, hy, he⟩ := hw
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

end ReeTwo.SylowModel
