module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCoordinates
/-!
# Finite coordinates for refined Ree two fiber counts

A polynomial formula for the cyclic action is proved on the core generators
and extended by multiplicativity. This gives a computational multiplication
with a proved equality to the original Sylow multiplication. Four binary
parametrizations identify the original candidates with `Fin 1024`: an explicit
left inverse proves injectivity, and the tail quotient computes their orders.

The final counting lemma sandwiches a centralizer between a list of commuting
elements and a list of conjugates. Its proof uses an injection from the product
of the conjugate list and the actual centralizer into the group.

Source: Shinoda (1975), (2.3), pp. 81–82, using the verified root relations in
`RootAction` and the candidate equations in `Order1024RefinedCoordinates`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.RefinedCounting
set_option maxRecDepth 16384

def countAction (x : Core) : Core where
  b0 := x.b0
  b1 := x.b0 + x.b1
  b2 := x.b0 + x.b1 + x.b2
  b3 := x.b1 + x.b3
  b4 := x.b0 + x.b1 + x.b3 + x.b4
  b5 := x.b0 + x.b0 * x.b1 + x.b5
  b6 := x.b0 + x.b1 + x.b0 * x.b1 + x.b5 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b6 + x.b7
  b8 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b5 + x.b6 + x.b7 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b4 + x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9

set_option maxHeartbeats 8000000 in
def countActionHom : Core →* Core where
  toFun := countAction
  map_one' := by decide +kernel
  map_mul' x y := by
    change countAction (Core.mul x y) = Core.mul (countAction x) (countAction y)
    apply Core.ext <;> simp only [countAction, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

theorem countAction_eq (x : Core) : countAction x = Core.a x := by
  have h : countActionHom = Core.a.toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot, countActionHom (Core.root i) = Core.a (Core.root i))
  exact DFunLike.congr_fun h x

def countAct (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  match t.toAdd.val with
  | 0 => x
  | 1 => countAction x
  | 2 => countAction (countAction x)
  | _ => countAction (countAction (countAction x))

theorem countAct_eq (t : FiveFour.Cyclic 4) (x : Core) :
    countAct t x = Core.complementAction (SemidirectProduct.inr t) x := by
  have ht : t = FiveFour.generator 4 ^ t.toAdd.val := by
    exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, t = FiveFour.generator 4 ^ t.toAdd.val) t
  conv_rhs => rw [ht, map_pow, map_pow]
  change _ = (Core.complementAction FiveFour.a ^ t.toAdd.val) x
  rw [Core.complementAction_a]
  have h : t.toAdd.val < 4 := ZMod.val_lt _
  interval_cases ht' : t.toAdd.val <;> simp [countAct, ht', countAction_eq, pow_succ]

def countMul (x y : SylowModel) : SylowModel :=
  ⟨Core.mul x.left (countAct x.right y.left), x.right * y.right⟩
theorem countMul_eq (x y : SylowModel) : countMul x y = x * y := by
  apply SemidirectProduct.ext
  · change Core.mul x.left (countAct x.right y.left) = _
    rw [countAct_eq]
    rfl
  · rfl


def countBit (n i : ℕ) : ZMod 2 := (n / 2^i : ℕ)
def countElement (c : Fin 4) (n : Fin 1024) : SylowModel :=
  let u := countBit n.val
  let tail : Core := ⟨0,0,0,0,u 4,u 5,u 6,u 7,u 8,u 9⟩
  match c.val with
  | 0 => ⟨{tail with b0 := u 3, b1 := u 0, b2 := u 1, b3 := u 2},
      Multiplicative.ofAdd (2 * (u 3).val)⟩
  | 1 => ⟨{tail with b0 := u 0, b1 := u 1, b2 := u 2, b3 := u 0 + u 1 + u 2 + u 3},
      Multiplicative.ofAdd (2 * (u 3).val)⟩
  | 2 => ⟨{tail with b0 := u 0, b1 := u 1, b2 := u 2, b3 := u 0 + u 1 + u 2},
      Multiplicative.ofAdd (2 * (u 3).val)⟩
  | _ => ⟨{tail with b0 := u 2, b1 := u 2 + u 3, b2 := u 0, b3 := u 1},
      Multiplicative.ofAdd ((u 2).val + 2 * (u 3).val)⟩

def countIndexNat (c : Fin 4) (x : SylowModel) : ℕ :=
  let b := x.left
  let t := x.right.toAdd.val
  let lead := match c.val with
    | 0 => b.b1.val + 2*b.b2.val + 4*b.b3.val + 8*(t/2)
    | 1 | 2 => b.b0.val + 2*b.b1.val + 4*b.b2.val + 8*(t/2)
    | _ => b.b2.val + 2*b.b3.val + 4*(t%2) + 8*(t/2)
  lead + 16*b.b4.val + 32*b.b5.val + 64*b.b6.val + 128*b.b7.val + 256*b.b8.val + 512*b.b9.val

theorem countIndex_lt (c : Fin 4) (x : SylowModel) : countIndexNat c x < 1024 := by
  have := ZMod.val_lt x.left.b0
  have := ZMod.val_lt x.left.b1
  have := ZMod.val_lt x.left.b2
  have := ZMod.val_lt x.left.b3
  have := ZMod.val_lt x.left.b4
  have := ZMod.val_lt x.left.b5
  have := ZMod.val_lt x.left.b6
  have := ZMod.val_lt x.left.b7
  have := ZMod.val_lt x.left.b8
  have := ZMod.val_lt x.left.b9
  have := ZMod.val_lt x.right.toAdd
  unfold countIndexNat
  dsimp only
  split <;> omega

def countIndex (c : Fin 4) (x : SylowModel) : Fin 1024 := ⟨countIndexNat c x, countIndex_lt c x⟩



theorem countElement_mem : ∀ c n, refinedTailMember c (TailQuotient.projection (countElement c n)) := by
  decide +kernel

theorem countIndex_element : ∀ c n, countIndex c (countElement c n) = n := by
  decide +kernel

theorem countCandidate_card (c : Fin 4) : Nat.card (residualCandidate (refinedIndex c)) = 1024 := by
  have hn : Nat.card (refinedTailNode c) = 16 := by
    change Nat.card {q : TailQuotient.Group // refinedTailMember c q} = 16
    rw [Nat.card_eq_fintype_card]
    exact (by decide +kernel : ∀ c, Fintype.card {q : TailQuotient.Group // refinedTailMember c q} = 16) c
  have hindex := (refinedTailNode c).index_mul_card
  rw [hn, TailQuotient.card] at hindex
  have hindex' : (residualCandidate (refinedIndex c)).index = 4 := by
    rw [refinedCandidate_eq_comap,
      Subgroup.index_comap_of_surjective (refinedTailNode c) TailQuotient.projection_surjective]
    omega
  have hcard := (residualCandidate (refinedIndex c)).index_mul_card
  rw [hindex', card] at hcard
  omega

noncomputable def countEquiv (c : Fin 4) : Fin 1024 ≃ residualCandidate (refinedIndex c) :=
  Equiv.ofBijective
    (fun n => ⟨countElement c n, (refinedCandidate_mem c _).mpr (countElement_mem c n)⟩)
    ((show Function.Injective (fun n => (⟨countElement c n,
      (refinedCandidate_mem c _).mpr (countElement_mem c n)⟩ : residualCandidate (refinedIndex c))) from by
      intro n m h
      have := congrArg (countIndex c) (congrArg Subtype.val h)
      simpa only [countIndex_element] using this).bijective_of_nat_card_le (by
        rw [countCandidate_card, Nat.card_fin]))
theorem centralizer_card_bounds {G : Type*} [Group G] [Finite G]
    {I J : Type*} [Finite I] [Finite J]
    (x : I → G) (hx : Function.Injective x) (w : I → G) (r : G)
    (hconj : ∀ i, x i * w i = w i * r)
    (z : J → G) (hz : Function.Injective z) (hcomm : ∀ j, z j * r = r * z j)
    (k : ℕ) (hpos : 0 < Nat.card I)
    (hprod : Nat.card I * k = Nat.card G) (hcard : Nat.card J = k) :
    Nat.card (Subgroup.centralizer ({r} : Set G)) = k := by
  let C := Subgroup.centralizer ({r} : Set G)
  let f : I × C → G := fun p => w p.1 * p.2.val
  have hf (p : I × C) : x p.1 * f p = f p * r := by
    change x p.1 * (w p.1 * p.2.val) = (w p.1 * p.2.val) * r
    rw [← mul_assoc, hconj, mul_assoc,
      ← Subgroup.mem_centralizer_singleton_iff.mp p.2.property, mul_assoc]
  have hinj : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := hx (mul_right_cancel (show x i * f (i,a) = x j * f (i,a) from by
      rw [hf (i,a), h, ← hf (j,b), ← h]))
    subst j
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
  have hu := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, ← hprod] at hu
  have hl := Nat.card_le_card_of_injective
    (fun j : J => (⟨z j, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm j)⟩ : C))
    (fun i j h => hz (congrArg Subtype.val h))
  rw [hcard] at hl
  exact le_antisymm (by nlinarith) hl
end ReeTwo.SylowModel.RefinedCounting
