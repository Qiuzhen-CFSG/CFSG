module
public import Theory.GroupAction.MarkedCubicRecognition.Models

/-!
# Recognition preserving the two cubic markings

Choose generators x and y in the two specified cubic subgroups. In the
Heisenberg case the map is explicitly x^b y^a [y,x]^c. Centrality of the
commutator proves multiplication, generation proves surjectivity, and
order 27 proves bijectivity. Checking the two generators proves
compatibility with both marked involutions. At order nine, multiplication
of the two cubic subgroups gives the elementary coordinates directly.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308 (1 March 2004 manuscript).
-/

@[expose] public section
namespace MarkedCubicRecognition
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {P : Type*} [Group P] [Finite P]

/-- Choose a generator of a specified cubic subgroup. -/
theorem exists_cubic_generator (A : Subgroup P) (hA : Nat.card A = 3) :
    ∃ x ∈ A, x ^ 3 = 1 ∧ zpowers x = A := by
  obtain ⟨x, hx⟩ := (ne_bot_iff_exists_ne_one (H := A)).mp
    (by intro hb; simp [hb] at hA)
  have hx3 : (x : P) ^ 3 = 1 := congrArg Subtype.val
    (show x ^ 3 = 1 by simpa only [hA] using pow_card_eq_one' (x := x))
  refine ⟨x, x.property, hx3, eq_of_le_of_card_ge (zpowers_le.mpr x.property) ?_⟩
  rw [hA, Nat.card_zpowers, orderOf_eq_prime hx3 (fun he => hx (Subtype.ext he))]

/-- The isomorphism is evaluated on the chosen marked generators and their
commutator. It preserves both cubic lines and both specified automorphisms. -/
theorem exists_heisenberg_equiv {A B : Subgroup P} {a b : MulAut P}
    (hm : MarkedCubicClassTwo.CubicMarking A B a b)
    (hcard : Nat.card P = 27) (hpow : ∀ x : P, x ^ 3 = 1)
    (hclass : _root_.commutator P ≤ center P) :
    ∃ e : HeisenbergPrime 3 ≃* P,
      leftAxis.range.map e.toMonoidHom = A ∧
      rightAxis.range.map e.toMonoidHom = B ∧
      (∀ z, e (leftFlip z) = a (e z)) ∧
      (∀ z, e (rightFlip z) = b (e z)) ∧
      ∃ x ∈ A, ∃ y ∈ B, ∀ z : HeisenbergPrime 3,
        e z = x ^ z.b.val * y ^ z.a.val * ⁅y, x⁆ ^ z.c.val := by
  obtain ⟨x, hxA, hx, hxgen⟩ := exists_cubic_generator A hm.card_left
  obtain ⟨y, hyB, hy, hygen⟩ := exists_cubic_generator B hm.card_right
  let c := ⁅y, x⁆
  have hc : c ∈ center P := hclass
    (Subgroup.commutator_mem_commutator (mem_top y) (mem_top x))
  have hs : y * x = c * x * y := by simp [c, commutatorElement_def, mul_assoc]
  let f := HeisenbergPrime.evaluateHom x y c hc hs hx hy (hpow c)
  have hfx : f leftGenerator = x := by
    simp [f, HeisenbergPrime.evaluateHom, leftGenerator, ZMod.val_one]
  have hfy : f rightGenerator = y := by
    simp [f, HeisenbergPrime.evaluateHom, rightGenerator, ZMod.val_one]
  have hfA : A ≤ f.range := by
    rw [← hxgen]
    exact zpowers_le.mpr ⟨leftGenerator, hfx⟩
  have hfB : B ≤ f.range := by
    rw [← hygen]
    exact zpowers_le.mpr ⟨rightGenerator, hfy⟩
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp
    (top_unique (hm.generate ▸ sup_le hfA hfB))
  have hbij : Function.Bijective f := hsurj.bijective_of_nat_card_le
    (by rw [HeisenbergPrime.card, hcard]; decide)
  let e := MulEquiv.ofBijective f hbij
  have heA : leftAxis.range.map e.toMonoidHom = A := by
    rw [← MonoidHom.range_comp]
    have heq : e.toMonoidHom.comp leftAxis = cyclicHom x hx := by
      ext z
      simp [e, f, HeisenbergPrime.evaluateHom, leftAxis, cyclicHom]
    rw [heq, cyclicHom_range (by decide), hxgen]
  have heB : rightAxis.range.map e.toMonoidHom = B := by
    rw [← MonoidHom.range_comp]
    have heq : e.toMonoidHom.comp rightAxis = cyclicHom y hy := by
      ext z
      simp [e, f, HeisenbergPrime.evaluateHom, rightAxis, cyclicHom]
    rw [heq, cyclicHom_range (by decide), hygen]
  have ha : e.toMonoidHom.comp leftFlip.toMonoidHom = a.toMonoidHom.comp e.toMonoidHom := by
    apply heisenberg_hom_ext
    · change e (leftFlip leftGenerator) = a (e leftGenerator)
      rw [show leftFlip leftGenerator = leftGenerator⁻¹ by
        ext <;> simp [leftFlip, leftGenerator], map_inv]
      change (f leftGenerator)⁻¹ = a (f leftGenerator)
      rw [hfx, hm.left_inverts x hxA]
    · change e (leftFlip rightGenerator) = a (e rightGenerator)
      rw [show leftFlip rightGenerator = rightGenerator by rfl]
      change f rightGenerator = a (f rightGenerator)
      rw [hfy, hm.left_fixes y hyB]
  have hb : e.toMonoidHom.comp rightFlip.toMonoidHom = b.toMonoidHom.comp e.toMonoidHom := by
    apply heisenberg_hom_ext
    · change e (rightFlip leftGenerator) = b (e leftGenerator)
      rw [show rightFlip leftGenerator = leftGenerator by rfl]
      change f leftGenerator = b (f leftGenerator)
      rw [hfx, hm.right_fixes x hxA]
    · change e (rightFlip rightGenerator) = b (e rightGenerator)
      rw [show rightFlip rightGenerator = rightGenerator⁻¹ by
        ext <;> simp [rightFlip, rightGenerator], map_inv]
      change (f rightGenerator)⁻¹ = b (f rightGenerator)
      rw [hfy, hm.right_inverts y hyB]
  exact ⟨e, heA, heB, DFunLike.congr_fun ha, DFunLike.congr_fun hb,
    x, hxA, y, hyB, fun _ => rfl⟩

/-- Cubic coordinates for the elementary alternative, preserving both lines
and the two independent inversions. -/
theorem exists_nine_equiv {A B : Subgroup P} {a b : MulAut P}
    (hm : MarkedCubicClassTwo.CubicMarking A B a b) (hcard : Nat.card P = 9) :
    ∃ e : Nine ≃* P,
      (MonoidHom.inl C3 C3).range.map e.toMonoidHom = A ∧
      (MonoidHom.inr C3 C3).range.map e.toMonoidHom = B ∧
      (∀ z, e (nineLeftFlip z) = a (e z)) ∧
      (∀ z, e (nineRightFlip z) = b (e z)) := by
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (by simpa using hcard)
  obtain ⟨x, hxA, hx, hxgen⟩ := exists_cubic_generator A hm.card_left
  obtain ⟨y, hyB, hy, hygen⟩ := exists_cubic_generator B hm.card_right
  let f := MonoidHom.noncommCoprod (cyclicHom x hx) (cyclicHom y hy)
    (fun _ _ => Commute.all _ _)
  have hf : f.range = ⊤ := by
    rw [MonoidHom.noncommCoprod_range, cyclicHom_range (by decide),
      cyclicHom_range (by decide), hxgen, hygen, hm.generate]
  have hbij := (MonoidHom.range_eq_top.mp hf).bijective_of_nat_card_le
    (show Nat.card Nine ≤ Nat.card P by simp [Nine, C3, hcard])
  let e := MulEquiv.ofBijective f hbij
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rw [← MonoidHom.range_comp]
    change (f.comp (MonoidHom.inl C3 C3)).range = A
    rw [MonoidHom.noncommCoprod_comp_inl, cyclicHom_range (by decide), hxgen]
  · rw [← MonoidHom.range_comp]
    change (f.comp (MonoidHom.inr C3 C3)).range = B
    rw [MonoidHom.noncommCoprod_comp_inr, cyclicHom_range (by decide), hygen]
  · intro z
    change cyclicHom x hx z.1⁻¹ * cyclicHom y hy z.2 =
      a (cyclicHom x hx z.1 * cyclicHom y hy z.2)
    rw [map_inv, map_mul, hm.left_inverts (cyclicHom x hx z.1) (A.pow_mem hxA _),
      hm.left_fixes (cyclicHom y hy z.2) (B.pow_mem hyB _)]
  · intro z
    change cyclicHom x hx z.1 * cyclicHom y hy z.2⁻¹ =
      b (cyclicHom x hx z.1 * cyclicHom y hy z.2)
    rw [map_inv, map_mul, hm.right_fixes (cyclicHom x hx z.1) (A.pow_mem hxA _),
      hm.right_inverts (cyclicHom y hy z.2) (B.pow_mem hyB _)]

private theorem exists_cubic_non_self_inverse (A : Subgroup P) (hA : Nat.card A = 3) :
    ∃ x ∈ A, x⁻¹ ≠ x := by
  obtain ⟨x, hxA, hx3, hxgen⟩ := exists_cubic_generator A hA
  refine ⟨x, hxA, fun hi => ?_⟩
  have hx2 : x * x = 1 := by simpa only [hi] using inv_mul_cancel x
  have hx1 : x = 1 := by simpa only [pow_succ, pow_zero, one_mul, hx2] using hx3
  rw [hx1, zpowers_one_eq_bot] at hxgen
  simp [← hxgen] at hA

/-- The two opposite inversions are distinct nontrivial automorphisms. -/
theorem marked_actions_distinct {A B : Subgroup P} {a b : MulAut P}
    (hm : MarkedCubicClassTwo.CubicMarking A B a b) : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨x, hxA, hxi⟩ := exists_cubic_non_self_inverse A hm.card_left
  obtain ⟨y, hyB, hyi⟩ := exists_cubic_non_self_inverse B hm.card_right
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    apply hxi
    simpa only [ha, MulAut.one_apply] using (hm.left_inverts x hxA).symm
  · intro hb
    apply hyi
    simpa only [hb, MulAut.one_apply] using (hm.right_inverts y hyB).symm
  · intro hab
    exact hxi ((hm.left_inverts x hxA).symm.trans
      ((DFunLike.congr_fun hab x).trans (hm.right_fixes x hxA)))

end MarkedCubicRecognition
