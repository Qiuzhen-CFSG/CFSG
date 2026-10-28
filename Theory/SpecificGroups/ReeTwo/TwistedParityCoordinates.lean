module

public import Theory.SpecificGroups.ReeTwo.MaximalParityProfiles
public import Theory.Frattini.BinarySquares

/-!
# Coordinates for the twisted Ree two parity kernel

For an element with core coordinates `b0,...,b9` and cyclic-four coordinate `t`,
the twisted parity condition says `b0 = t mod 2`. Write `h = floor(t / 2)`.
The three quotient coordinates are `(t mod 2, b1 + h, b2 + b3 + h)`.
The carry in addition modulo four cancels the change of the leading core
coordinates under the root-one action. This proves additivity on the kernel.
The ordered lifts are `rootOne * root 0`, `root 1`, and `root 2`.

This module constructs the surjective map and proves that its order-256 kernel
contains the Frattini subgroup. Identifying that kernel with the Frattini
subgroup and computing its power fibers are separate statements.

Source: Shinoda (1975), (2.3), pp. 81–82, with the root conventions verified
in `Core`, `RootAction`, `Sylow`, and `MaximalCharacters`. All finite
certificates below are reduced by the Lean kernel.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private abbrev V := TwistedParityQuotient

private def head : Core →* V where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b2 + x.b3]
  map_one' := by decide +kernel
  map_mul' x y := by
    change (![x.b0 + y.b0, x.b1 + y.b1, (x.b2 + y.b2) + (x.b3 + y.b3)] : Fin 3 → ZMod 2) = _ + _
    ext i
    fin_cases i
    · rfl
    · rfl
    · change (x.b2 + y.b2) + (x.b3 + y.b3) = (x.b2 + x.b3) + (y.b2 + y.b3)
      ring

private def low (t : FiveFour.Cyclic 4) : ZMod 2 := (parity t).toAdd
private def high (t : FiveFour.Cyclic 4) : ZMod 2 := (t.toAdd.val / 2 : ℕ)

private def headAction (t : FiveFour.Cyclic 4) : V →* V where
  toFun x := Multiplicative.ofAdd ![x.toAdd 0, x.toAdd 1 + low t * x.toAdd 0,
    x.toAdd 2 + low t * x.toAdd 0]
  map_one' := by
    change (![0, _, _] : Fin 3 → ZMod 2) = 0
    ext i
    fin_cases i <;> simp
  map_mul' x y := by
    change (![(x*y).toAdd 0, _, _] : Fin 3 → ZMod 2) = _ + _
    ext i
    fin_cases i <;> simp <;> ring

private theorem head_action_hom (t : FiveFour.Cyclic 4) :
    head.comp (Core.complementAction (SemidirectProduct.inr t)).toMonoidHom =
      (headAction t).comp head := by
  apply Core.hom_ext
  exact (by decide +kernel : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot),
    head (Core.complementAction (SemidirectProduct.inr t) (Core.root i)) =
      headAction t (head (Core.root i))) t

private theorem head_mul (x y : SylowModel) :
    head (x*y).left = head x.left * headAction x.right (head y.left) := by
  change head (x.left * Core.complementAction (SemidirectProduct.inr x.right) y.left) = _
  rw [map_mul]
  exact congrArg (head x.left * ·) (DFunLike.congr_fun (head_action_hom x.right) y.left)

private def raw (t : FiveFour.Cyclic 4) (v : V) : V :=
  Multiplicative.ofAdd ![low t, v.toAdd 1 + high t, v.toAdd 2 + high t]

private theorem raw_mul : ∀ (t u : FiveFour.Cyclic 4) (v w : V),
    w.toAdd 0 = low u →
    raw (t*u) (v * headAction t w) = raw t v * raw u w := by decide +kernel

/-- Membership in the twisted kernel identifies its first core coordinate with parity. -/
public theorem mem_twistedParityKernel (g : SylowModel) :
    g ∈ (maximalCharacter 1 1 0).ker ↔ g.left.b0 = (parity g.right).toAdd := by
  simp only [MonoidHom.mem_ker, maximalCharacter, ZMod.val_one, ZMod.val_zero,
    pow_one, pow_zero, mul_one, MonoidHom.mul_apply]
  change parity g.right * Multiplicative.ofAdd g.left.b0 = 1 ↔ _
  exact (by decide +kernel : ∀ (t : FiveFour.Cyclic 4) (b : ZMod 2),
    parity t * Multiplicative.ofAdd b = 1 ↔ b = low t) g.right g.left.b0

/-- The three corrected binary coordinates on the twisted parity kernel. -/
@[expose] public def twistedParityCoordinates :
    (maximalCharacter 1 1 0).ker →* TwistedParityQuotient where
  toFun g := Multiplicative.ofAdd ![(parity g.val.right).toAdd,
    g.val.left.b1 + (g.val.right.toAdd.val / 2 : ℕ),
    g.val.left.b2 + g.val.left.b3 + (g.val.right.toAdd.val / 2 : ℕ)]
  map_one' := by decide +kernel
  map_mul' x y := by
    change raw (x.val.right * y.val.right) (head (x.val*y.val).left) = _
    rw [head_mul]
    exact raw_mul _ _ _ _ ((mem_twistedParityKernel y.val).mp y.property)

/-- Ordered representatives in the basis specified by `twistedParityProfile`. -/
@[expose] public def twistedParityRepresentative (v : TwistedParityQuotient) : SylowModel :=
  (rootOne * root 0) ^ (v.toAdd 0).val * root 1 ^ (v.toAdd 1).val * root 2 ^ (v.toAdd 2).val

/-- Every ordered representative belongs to the twisted parity kernel. -/
public theorem twistedParityRepresentative_mem :
    ∀ v, twistedParityRepresentative v ∈ (maximalCharacter 1 1 0).ker := by decide +kernel

/-- The ordered representatives recover every binary vector. -/
public theorem twistedParityCoordinates_representative : ∀ v,
    twistedParityCoordinates ⟨twistedParityRepresentative v, twistedParityRepresentative_mem v⟩ = v :=
  by decide +kernel

/-- The twisted coordinate map is onto the rank-three binary group. -/
public theorem twistedParityCoordinates_surjective : Function.Surjective twistedParityCoordinates :=
  fun v => ⟨⟨twistedParityRepresentative v, twistedParityRepresentative_mem v⟩,
    twistedParityCoordinates_representative v⟩

/-- Explicit evaluation, including the high-bit correction from the cyclic factor. -/
public theorem twistedParityCoordinates_apply (g : (maximalCharacter 1 1 0).ker) :
    twistedParityCoordinates g = Multiplicative.ofAdd
      ![(parity g.val.right).toAdd,
        g.val.left.b1 + (g.val.right.toAdd.val / 2 : ℕ),
        g.val.left.b2 + g.val.left.b3 + (g.val.right.toAdd.val / 2 : ℕ)] := rfl

/-- The elementary abelian coordinate target kills all Frattini generators. -/
public theorem frattini_le_twistedParityCoordinates_ker :
    frattini (maximalCharacter 1 1 0).ker ≤ twistedParityCoordinates.ker := by
  rw [(IsPGroup.of_card (n := 11)
    (maximalCharacter_ker_card 1 1 0 (by decide))).frattini_eq_closure_squares]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  change twistedParityCoordinates (x ^ 2) = 1
  rw [map_pow]
  exact (by decide +kernel : ∀ v : TwistedParityQuotient, v ^ 2 = 1) _

/-- The coordinate kernel has order 256. -/
public theorem twistedParityCoordinates_ker_card : Nat.card twistedParityCoordinates.ker = 256 := by
  have hi : twistedParityCoordinates.ker.index = 8 := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr twistedParityCoordinates_surjective]
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    rw [Nat.card_fun]
    simp
  have hc := twistedParityCoordinates.ker.index_mul_card
  rw [hi, maximalCharacter_ker_card 1 1 0 (by decide)] at hc
  omega

/-- The cyclic-four coordinate and the last nine core coordinates are free parameters. -/
@[expose] public def twistedParityParameterEquiv : (maximalCharacter 1 1 0).ker ≃
    (FiveFour.Cyclic 4 × (Fin 9 → ZMod 2)) where
  toFun g := (g.val.right, ![g.val.left.b1, g.val.left.b2, g.val.left.b3,
    g.val.left.b4, g.val.left.b5, g.val.left.b6, g.val.left.b7, g.val.left.b8, g.val.left.b9])
  invFun p := ⟨⟨⟨(parity p.1).toAdd, p.2 0, p.2 1, p.2 2, p.2 3,
    p.2 4, p.2 5, p.2 6, p.2 7, p.2 8⟩, p.1⟩, (mem_twistedParityKernel _).mpr rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Core.ext <;> try rfl
      exact ((mem_twistedParityKernel g.val).mp g.property).symm
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl

end ReeTwo.SylowModel
