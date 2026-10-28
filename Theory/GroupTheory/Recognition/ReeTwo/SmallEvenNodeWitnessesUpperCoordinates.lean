module

public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Projected orbit certificates for the upper small even nodes

The even Sylow coordinates have a triangular multiplication law. Truncating
trailing core coordinates therefore preserves the left action of every even
element. A finite orbit containing the identity and closed under the node
generators contains the generated subgroup's image; a missing projected point
certifies nonmembership. Finiteness supplies inverse stability.

The polynomial even action below follows the checked calculation in
`ParityFrattiniPowerCounts`. Positive square-word equations are transported
back to the original Sylow group, then used by the Frattini witness criterion.

Source: Shinoda (1975), (2.3), pp. 81–82; the root and multiplication conventions
of `ReeTwo.Core`, `RootAction`, and `Sylow`. All finite equations are checked
by the Lean kernel.
-/

namespace ReeTwo.SylowModel.UpperCertificate
private theorem outside_of_invariant {G : Type*} [Group G] [Finite G] {n : ℕ}
    (gen : Fin n → G) (s : Set G) (hone : 1 ∈ s)
    (hstep : ∀ i, Set.MapsTo (gen i * ·) s s)
    (g : G) (hout : g ∉ s) : g ∉ Subgroup.closure (Set.range gen) := by
  have hinv (i : Fin n) : Set.MapsTo ((gen i)⁻¹ * ·) s s := by
    have hs := ((Set.toFinite s).injOn_iff_bijOn_of_mapsTo (hstep i)).mp
      (mul_right_injective (gen i)).injOn
    intro x hx
    obtain ⟨y, hy, he⟩ := hs.surjOn hx
    change (gen i)⁻¹ * x ∈ s
    rw [← he]
    simpa only [inv_mul_cancel_left] using hy
  have hm : ∀ x, x ∈ Subgroup.closure (Set.range gen) → x ∈ s := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact hone
    | mul_left x hx y _ ih =>
      obtain ⟨i, rfl⟩ := hx
      exact hstep i ih
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨i, rfl⟩ := hx
      exact hinv i ih
  exact fun hg => hout (hm g hg)
@[expose] public section

def evenAction (x : Core) : Core where
  b0 := x.b0
  b1 := x.b1
  b2 := x.b0 + x.b2
  b3 := x.b0 + x.b3
  b4 := x.b0 + x.b1 + x.b4
  b5 := x.b0 + x.b5
  b6 := x.b0 + x.b0 * x.b1 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b0 * x.b2 + x.b5 + x.b7
  b8 := x.b1 + x.b0 * x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b0 * x.b3 + x.b5 + x.b6 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b0 * x.b1 * x.b3 + x.b0 * x.b4 + x.b5 + x.b9

private def evenHom : Core →* Core where
  toFun := evenAction
  map_one' := by decide +kernel
  map_mul' x y := by
    change evenAction (Core.mul x y) = Core.mul (evenAction x) (evenAction y)
    apply Core.ext <;> simp only [evenAction, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

set_option maxRecDepth 8192 in
private theorem evenAction_eq (x : Core) :
    evenAction x = (Core.a ^ 2) x := by
  have h : evenHom = (Core.a ^ 2).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot, evenHom (Core.root i) = (Core.a ^ 2) (Core.root i))
  exact DFunLike.congr_fun h x

private theorem even_complement (b : ZMod 2) (x : Core) :
    Core.complementAction (SemidirectProduct.inr
      (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4)) x =
      if b = 0 then x else evenAction x := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · have h : (Multiplicative.ofAdd (2 * (0 : ZMod 2).val) : FiveFour.Cyclic 4) = 1 := rfl
    rw [h, map_one, map_one, MulAut.one_apply, if_pos rfl]
  · have h : (Multiplicative.ofAdd (2 * (1 : ZMod 2).val) : FiveFour.Cyclic 4) =
        FiveFour.generator 4 ^ 2 := by decide
    rw [h, map_pow, map_pow]
    change (Core.complementAction FiveFour.a ^ 2) x = _
    rw [Core.complementAction_a, ← evenAction_eq, if_neg (by decide)]


abbrev E := Core × ZMod 2
def encode (x : E) : SylowModel := ⟨x.1, Multiplicative.ofAdd (2 * x.2.val)⟩
def mul (x y : E) : E := (Core.mul x.1 (if x.2 = 0 then y.1 else evenAction y.1), x.2 + y.2)
theorem encode_mul (x y : E) : encode (mul x y) = encode x * encode y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.1 * ·) (even_complement x.2 y.1).symm
  · exact (by decide +kernel : ∀ a b : ZMod 2,
      (Multiplicative.ofAdd (2 * (a + b).val) : FiveFour.Cyclic 4) =
      Multiplicative.ofAdd (2 * a.val : ZMod 4) * Multiplicative.ofAdd (2 * b.val : ZMod 4)) x.2 y.2
theorem encode_injective : Function.Injective encode := by
  intro x y h
  have hl := congrArg SemidirectProduct.left h
  have hr := congrArg SemidirectProduct.right h
  have hi : Function.Injective (fun a : ZMod 2 => (Multiplicative.ofAdd (2 * a.val) : FiveFour.Cyclic 4)) := by decide +kernel
  exact Prod.ext hl (hi hr)
def one : E := (1,0)
theorem encode_one : encode one = 1 := rfl
def word {n : ℕ} (gen : Fin n → E) : List (Fin n) → E
   | [] => one
   | i :: is => mul (gen i) (word gen is)
theorem encode_word {n : ℕ} (gen : Fin n → E) (w : List (Fin n)) :
     encode (word gen w) = Theory.GroupTheory.evalWord (encode ∘ gen) w := by
   induction w with
   | nil => rfl
   | cons i is ih => exact (encode_mul _ _).trans (congrArg (encode (gen i) * ·) ih)
def squareWord {n : ℕ} (gen : Fin n → E) : List (List (Fin n)) → E
   | [] => one
   | w :: ws => mul (mul (word gen w) (word gen w)) (squareWord gen ws)
theorem encode_squareWord {n : ℕ} (gen : Fin n → E) (ws : List (List (Fin n))) :
     encode (squareWord gen ws) = Subgroup.evalSquareWord (encode ∘ gen) ws := by
   induction ws with
   | nil => rfl
   | cons w ws ih => simp only [squareWord, encode_mul, encode_word, ih,
       Subgroup.evalSquareWord, List.map_cons, List.prod_cons, pow_two]
theorem checked_displacements {n : ℕ} (gen : Fin n → E) (g : E)
     (ws : Fin n → List (List (Fin n)))
     (h : ∀ i, mul (mul (gen i) (squareWord gen (ws i))) g = mul g (gen i)) :
     ∀ i, Subgroup.evalSquareWord (encode ∘ gen) (ws i) =
       (encode (gen i))⁻¹ * (encode g * encode (gen i) * (encode g)⁻¹) := by
   intro i
   have he := congrArg encode (h i)
   simp only [encode_mul, encode_squareWord] at he
   apply (mul_left_cancel_iff (a := encode (gen i))).mp
   apply (mul_right_cancel_iff (a := encode g)).mp
   simpa only [mul_inv_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using he

def trunc (k : Fin 11) (x : E) : E :=
  (⟨if 0 < k.val then x.1.b0 else 0, if 1 < k.val then x.1.b1 else 0,
    if 2 < k.val then x.1.b2 else 0, if 3 < k.val then x.1.b3 else 0,
    if 4 < k.val then x.1.b4 else 0, if 5 < k.val then x.1.b5 else 0,
    if 6 < k.val then x.1.b6 else 0, if 7 < k.val then x.1.b7 else 0,
    if 8 < k.val then x.1.b8 else 0, if 9 < k.val then x.1.b9 else 0⟩, x.2)
theorem trunc_mul_right (k : Fin 11) (x y : E) :
     trunc k (mul x y) = trunc k (mul x (trunc k y)) := by
  fin_cases k <;> by_cases h : x.2 = 0 <;>
    simp [trunc, mul, h, evenAction, Core.mul]
theorem outside_of_projected_orbit {n m : ℕ} (gen : Fin n → E)
    (k : Fin 11) (rep : Fin m → E) (base : Fin m)
    (hbase : rep base = trunc k one) (next : Fin n → Fin m → Fin m)
    (hnext : ∀ i j, trunc k (mul (gen i) (rep j)) = rep (next i j))
    (g : E) (hout : ∀ j, rep j ≠ trunc k g) :
    encode g ∉ Subgroup.closure (Set.range (encode ∘ gen)) := by
  let s : Set SylowModel := {x | ∃ e : E, encode e = x ∧ trunc k e ∈ Set.range rep}
  apply outside_of_invariant (encode ∘ gen) s
  · exact ⟨one, encode_one, base, hbase⟩
  · intro i x hx
    obtain ⟨e, rfl, j, hj⟩ := hx
    refine ⟨mul (gen i) e, encode_mul _ _, next i j, ?_⟩
    rw [trunc_mul_right, ← hj, hnext]
  · rintro ⟨e, he, j, hj⟩
    have he' := encode_injective he
    exact hout j (he' ▸ hj)
end
end ReeTwo.SylowModel.UpperCertificate
