module

public import Theory.GroupAction.C4SquareMaximalTwoAction

/-!
# A central binary action in an order-sixteen C₄-square action

A two-subgroup of order sixteen fixes a nonzero involution of the C₄-square.
Its index in that involution's stabilizer is at most two. The stabilizer's
central transvection is a square there, hence belongs to the given subgroup.
This transvection has surjective norms onto the involutions. Furthermore, a
nonidentity action fixing every involution and inverting no element of order
four can fix a nonbinary point of the transvection only if it is that
transvection itself. The coordinate certificates are checked by `decide`.

This refines the stabilizer calculation in `C4SquareMaximalTwoAction` for
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

set_option synthInstance.maxSize 4096
open Subgroup
namespace C4SquareExtension.SixteenInverted

private def u : Model := (Multiplicative.ofAdd 1, 1)
private def v : Model := (1, Multiplicative.ofAdd 1)

private def eval (a b x : Model) : Model := a ^ x.1.toAdd.val * b ^ x.2.toAdd.val
private theorem eval_std : ∀ x : Model, eval u v x = x := by decide
private theorem hom_eval (f : MulAut Model) (x : Model) :
    f x = eval (f u) (f v) x := by
  conv_lhs => rw [← eval_std x]
  simp only [eval, map_mul, map_pow]
private theorem aut_ext {f g : MulAut Model} (hu : f u = g u)
    (hv : f v = g v) : f = g := by
  apply MulEquiv.ext
  intro x
  rw [hom_eval f, hom_eval g, hu, hv]

private def Good (p : Model × Model) : Prop :=
  p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.1 ^ 2 ≠ p.2 ^ 2
private theorem good_aut (f : MulAut Model) : Good (f u, f v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (by decide : u ^ 2 ≠ 1) (f.injective (by simpa only [map_pow, map_one] using h))
  · intro h
    exact (by decide : v ^ 2 ≠ 1) (f.injective (by simpa only [map_pow, map_one] using h))
  · intro h
    exact (by decide : u ^ 2 ≠ v ^ 2) (f.injective (by simpa only [map_pow] using h))

private def transvection (z x : Model) : Model :=
  if z = u ^ 2 then (x.1 * x.2 ^ 2, x.2)
  else if z = v ^ 2 then (x.1, x.2 * x.1 ^ 2)
  else (x.1⁻¹ * x.2 ^ 2, x.1 ^ 2 * x.2⁻¹)
private theorem transvection_invol : ∀ z x : Model,
    transvection z (transvection z x) = x := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem transvection_mul : ∀ z x y : Model,
    transvection z (x * y) = transvection z x * transvection z y := by decide
private def centralAut (z : Model) : MulAut Model where
  toFun := transvection z
  invFun := transvection z
  left_inv := transvection_invol z
  right_inv := transvection_invol z
  map_mul' := transvection_mul z
private theorem fixes_binary : ∀ z x : Model,
    x ^ 2 = 1 → transvection z x = x := by decide
private theorem inverts_only_binary : ∀ z x : Model,
    transvection z x = x⁻¹ → x ^ 2 = 1 := by decide
private theorem nonidentity : ∀ z : Model,
    transvection z u ≠ u ∨ transvection z v ≠ v := by decide
private theorem norm_surjective : ∀ z s : Model, s ^ 2 = 1 →
    ∃ d : Model, d * transvection z d = s := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem central_certificate : ∀ z a b : Model,
    z ^ 2 = 1 → z ≠ 1 → Good (a,b) → eval a b z = z →
    transvection z a = eval a b (transvection z u) ∧
      transvection z b = eval a b (transvection z v) := by
  unfold Good
  decide

private def root (z x : Model) : Model :=
  if z = u ^ 2 then (x.1 * x.2, x.2)
  else if z = v ^ 2 then (x.1, x.1 * x.2)
  else (x.2, x.1⁻¹ * x.2 ^ 2)
private theorem root_four : ∀ z x : Model, root z (root z (root z (root z x))) = x := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem root_mul : ∀ z x y : Model,
    root z (x * y) = root z x * root z y := by decide
private def rootAut (z : Model) : MulAut Model where
  toFun := root z
  invFun x := root z (root z (root z x))
  left_inv := root_four z
  right_inv := root_four z
  map_mul' := root_mul z
private theorem root_square (z : Model) : rootAut z ^ 2 = centralAut z := by
  apply MulEquiv.ext
  exact (by decide : ∀ z x : Model, root z (root z x) = transvection z x) z
private theorem root_fixed : ∀ z : Model, z ^ 2 = 1 → z ≠ 1 → root z z = z := by decide

private abbrev Bits := Fin 2 × Fin 2 × Fin 2 × Fin 2
private def act (m : Bits) (x : Model) : Model :=
  (Multiplicative.ofAdd ((1 + 2 * (m.1.val : ZMod 4)) * x.1.toAdd +
    2 * (m.2.1.val : ZMod 4) * x.2.toAdd),
   Multiplicative.ofAdd (2 * (m.2.2.1.val : ZMod 4) * x.1.toAdd +
    (1 + 2 * (m.2.2.2.val : ZMod 4)) * x.2.toAdd))
private theorem encode (f : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x) : ∃ m : Bits, ∀ x, f x = act m x := by
  have hu : f u ^ 2 = u ^ 2 := by rw [← map_pow]; exact hf _ (by decide)
  have hv : f v ^ 2 = v ^ 2 := by rw [← map_pow]; exact hf _ (by decide)
  have hc : ∀ a b : Model, a ^ 2 = u ^ 2 → b ^ 2 = v ^ 2 →
      ∃ m : Bits, a = act m u ∧ b = act m v := by decide
  obtain ⟨m, hm, hn⟩ := hc (f u) (f v) hu hv
  refine ⟨m, fun x => ?_⟩
  rw [hom_eval, hm, hn]
  exact (by decide : ∀ m : Bits, ∀ x : Model, eval (act m u) (act m v) x = act m x) m x
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem detection_certificate : ∀ z s : Model, ∀ m : Bits,
    (act m u ≠ u ∨ act m v ≠ v) →
    (∀ x : Model, act m x = x⁻¹ → x ^ 2 = 1) →
    s ^ 2 ≠ 1 → transvection z s = s → act m s = s →
    act m u = transvection z u ∧ act m v = transvection z v := by decide

/-- Every order-sixteen two-action contains a central transvection with norm
correction and detection of bad actions on its nonbinary fixed points. -/
public theorem exists_central_action (C : Subgroup (MulAut Model))
    (hC : IsPGroup 2 C) (hc : Nat.card C = 16) :
    ∃ a : MulAut Model, a ∈ C ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
      (∀ x : Model, x ^ 2 = 1 → a x = x) ∧
      (∀ f ∈ C, Commute f a) ∧
      (∀ x : Model, a x = x⁻¹ → x ^ 2 = 1) ∧
      (∀ x : Model, x ^ 2 = 1 → ∃ d : Model, d * a d = x) ∧
      (∀ f : MulAut Model, f ≠ 1 →
        (∀ x : Model, x ^ 2 = 1 → f x = x) →
        (∀ x : Model, f x = x⁻¹ → x ^ 2 = 1) →
        ∀ s : Model, s ^ 2 ≠ 1 → a s = s → f s = s → f = a) := by
  let X : SubMulAction C Model := {
    carrier := {x | x ^ 2 = 1 ∧ x ≠ 1}
    smul_mem' := by
      intro a x hx
      constructor
      · change ((a : MulAut Model) x) ^ 2 = 1
        rw [← map_pow, hx.1, map_one]
      · intro h
        exact hx.2 ((a : MulAut Model).injective (h.trans (map_one a.val).symm)) }
  have hcard : Nat.card X = 3 := by
    change Nat.card {x : Model // x ^ 2 = 1 ∧ x ≠ 1} = 3
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨z, hz⟩ := hC.nonempty_fixed_point_of_prime_not_dvd_card X (by rw [hcard]; decide)
  let T := MulAction.stabilizer (MulAut Model) z.val
  have hCT : C ≤ T := by
    intro a ha
    change a z.val = z.val
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hz ⟨a, ha⟩)
  let H := C.subgroupOf T
  have hH : Nat.card H = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv]
    exact hc
  have hi : H.index = 1 ∨ H.index = 2 := by
    have hm := H.card_mul_index
    have ht := model_stabilizer_card_le z.val z.property.1 z.property.2
    have hp : 0 < Nat.card T := Nat.card_pos
    rw [hH] at hm
    change 16 * H.index = Nat.card (MulAction.stabilizer (MulAut Model) z.val) at hm
    change 0 < Nat.card (MulAction.stabilizer (MulAut Model) z.val) at hp
    omega
  have hroot : rootAut z.val ∈ T := root_fixed z.val z.property.1 z.property.2
  have haC : centralAut z.val ∈ C := by
    have hs : (⟨rootAut z.val, hroot⟩ : T) ^ 2 ∈ H := by
      rcases hi with hi | hi
      · rw [index_eq_one.mp hi]; trivial
      · exact H.sq_mem_of_index_two hi _
    change rootAut z.val ^ 2 ∈ C at hs
    rwa [root_square] at hs
  refine ⟨centralAut z.val, haC, ?_, ?_, fixes_binary z.val, ?_,
    inverts_only_binary z.val, norm_surjective z.val, ?_⟩
  · intro heq
    rcases nonidentity z.val with h | h
    · exact h (congrArg (fun a : MulAut Model => a u) heq)
    · exact h (congrArg (fun a : MulAut Model => a v) heq)
  · apply MulEquiv.ext
    exact transvection_invol z.val
  · intro f hf
    have hh := central_certificate z.val (f u) (f v) z.property.1 z.property.2
      (good_aut f) ((hom_eval f z.val).symm.trans (hCT hf))
    apply aut_ext
    · change f (centralAut z.val u) = centralAut z.val (f u)
      rw [hom_eval f]
      exact hh.1.symm
    · change f (centralAut z.val v) = centralAut z.val (f v)
      rw [hom_eval f]
      exact hh.2.symm
  · intro f hf hfix hinv s hs has hfs
    obtain ⟨m, hm⟩ := encode f hfix
    have hmne : act m u ≠ u ∨ act m v ≠ v := by
      by_contra! h
      exact hf (aut_ext ((hm u).trans h.1) ((hm v).trans h.2))
    have hminv : ∀ x : Model, act m x = x⁻¹ → x ^ 2 = 1 := by
      intro x hx
      exact hinv x ((hm x).trans hx)
    obtain ⟨hu, hv⟩ := detection_certificate z.val s m hmne hminv hs has
      ((hm s).symm.trans hfs)
    exact aut_ext ((hm u).trans hu) ((hm v).trans hv)

end C4SquareExtension.SixteenInverted
