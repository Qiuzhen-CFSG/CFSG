module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.RankOne

/-!
# Lifting the binary tetrahedral wreath product

The model is (SL₂(3) × SL₂(3)) ⋊ C₂, with C₂ interchanging the factors.
It has order 1152. In a central two-extension, the two binary tetrahedral
factors lift uniquely and their lifts commute. If the image of the swap
is conjugate to the central involution in the first factor, that conjugacy
provides an involutory lift of the swap. Uniqueness of rank-one lifts forces
the two conjugation relations, so the semidirect-product universal property
constructs a lift of the entire wreath product.

All hypotheses refer to the specified homomorphism into the base group.
The symplectic application still needs an actual matrix embedding and the
specified involution fusion. Its order gives index 45 in Sp₄(3), allowing
central transfer. No matrix embedding is asserted in this module.

Source: the two-local calculation for the ternary symplectic multiplier,
Aschbacher–Smith I.1.4(1), printed p.408, and GLS3 §6.1; rank-one relations
come from `TwoPrimary.RankOne` and its binary tetrahedral sources.
-/

public section

open GLS3.Chapter5.SchurPresentation
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary

abbrev C2 := Multiplicative (ZMod 2)

private theorem c2_cases (x : C2) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  exact (by decide : ∀ y : C2, y = 1 ∨ y = Multiplicative.ofAdd 1) x

@[expose] def swapAction : C2 →* MulAut (BinaryTetrahedral × BinaryTetrahedral) where
  toFun t := if t = 1 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' x y := by
    rcases c2_cases x with rfl | rfl <;> rcases c2_cases y with rfl | rfl
    all_goals apply MulEquiv.ext; intro z
    all_goals rfl

abbrev Wreath := (BinaryTetrahedral × BinaryTetrahedral) ⋊[swapAction] C2

@[expose] def leftFactor : BinaryTetrahedral →* Wreath :=
  SemidirectProduct.inl.comp (MonoidHom.inl _ _)

@[expose] def rightFactor : BinaryTetrahedral →* Wreath :=
  SemidirectProduct.inl.comp (MonoidHom.inr _ _)

@[expose] def swap : Wreath := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] def planeInvolution : Wreath := leftFactor (binaryI^2)

theorem wreath_card : Nat.card Wreath = 1152 := by
  rw [SemidirectProduct.card, Nat.card_prod, binaryTetrahedral_card]
  norm_num

theorem planeInvolution_square : planeInvolution ^ 2 = 1 := by
  rw [planeInvolution, ← map_pow, show (binaryI^2)^2 = 1 by decide, map_one]

theorem swap_square : swap ^ 2 = 1 := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd 1) : Wreath)^2 = 1
  rw [← map_pow, show (Multiplicative.ofAdd 1 : C2)^2 = 1 by decide, map_one]

theorem swap_left (x : BinaryTetrahedral) : swap * leftFactor x * swap⁻¹ = rightFactor x := by
  change SemidirectProduct.inr (Multiplicative.ofAdd 1) * SemidirectProduct.inl (x,1) *
    (SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ = SemidirectProduct.inl (1,x)
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem swap_right (x : BinaryTetrahedral) : swap * rightFactor x * swap⁻¹ = leftFactor x := by
  change SemidirectProduct.inr (Multiplicative.ofAdd 1) * SemidirectProduct.inl (1,x) *
    (SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ = SemidirectProduct.inl (x,1)
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem factors_commute (x y : BinaryTetrahedral) : Commute (leftFactor x) (rightFactor y) := by
  change SemidirectProduct.inl (x,1) * SemidirectProduct.inl (1,y) =
    (SemidirectProduct.inl (1,y) : Wreath) * SemidirectProduct.inl (x,1)
  rw [← map_mul, ← map_mul]
  simp

/-- Commutation of two binary tetrahedral images lifts through a central two-kernel. -/
theorem binary_lifts_commute {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (s t : BinaryTetrahedral →* E)
    (hcomm : ∀ a b, Commute (f (s a)) (f (t b)))
    (a b : BinaryTetrahedral) : Commute (s a) (t b) := by
  have hm (x : BinaryTetrahedral) : ⁅s x,t b⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (hcomm x b).commutator_eq
  let d : BinaryTetrahedral →* f.ker := {
    toFun x := ⟨⁅s x,t b⁆, hm x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ⁅s (x*y),t b⁆ = ⁅s x,t b⁆ * ⁅s y,t b⁆
      rw [map_mul]
      have hy := mem_center_iff.mp (hc (hm y)) (s x)
      rw [commutatorElement_mul_left_eq_conj_mul, hy, mul_inv_cancel_right]
      exact mem_center_iff.mp (hc (hm x)) ⁅s y,t b⁆ }
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (congrArg (fun k : BinaryTetrahedral →* f.ker => (k a : E)) (binary_hom_eq_one hk d))

/-- The swap fusion relation makes the full rank-one wreath product lift. -/
theorem exists_wreath_lift {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (j : Wreath →* G)
    (hfusion : ∃ g : G, g * j planeInvolution * g⁻¹ = j swap) :
    ∃ s : Wreath →* E, f.comp s = j := by
  obtain ⟨l,hl⟩ := exists_binary_lift f hf hc hk (j.comp leftFactor)
  obtain ⟨r,hr⟩ := exists_binary_lift f hf hc hk (j.comp rightFactor)
  have hl' (x) : f (l x) = j (leftFactor x) := DFunLike.congr_fun hl x
  have hr' (x) : f (r x) = j (rightFactor x) := DFunLike.congr_fun hr x
  have hcomm (x y) : Commute (l x) (r y) := binary_lifts_commute f hc hk l r
    (fun a b => by rw [hl', hr']; exact (factors_commute a b).map j) x y
  obtain ⟨g,hg⟩ := hf hfusion.choose
  let t := g * l (binaryI^2) * g⁻¹
  have ht : t^2 = 1 := by
    have hl2 : l (binaryI^2)^2 = 1 := by
      rw [← map_pow, show (binaryI^2)^2 = 1 by decide, map_one]
    calc
      t^2 = g * (l (binaryI^2)^2) * g⁻¹ := by dsimp only [t]; simp only [pow_two]; group
      _ = 1 := by rw [hl2]; group
  have hft : f t = j swap := by
    dsimp [t]
    rw [map_mul, map_mul, map_inv, hg, hl']
    exact hfusion.choose_spec
  have htl (x) : t * l x * t⁻¹ = r x := by
    have h := binary_lift_unique f hc hk ((MulAut.conj t).toMonoidHom.comp l) r (by
      apply MonoidHom.ext
      intro y
      change f (t*l y*t⁻¹) = f (r y)
      rw [map_mul, map_mul, map_inv, hft, hl', hr', ← map_inv, ← map_mul, ← map_mul,
        swap_left])
    exact DFunLike.congr_fun h x
  have htr (x) : t * r x * t⁻¹ = l x := by
    have h := binary_lift_unique f hc hk ((MulAut.conj t).toMonoidHom.comp r) l (by
      apply MonoidHom.ext
      intro y
      change f (t*r y*t⁻¹) = f (l y)
      rw [map_mul, map_mul, map_inv, hft, hl', hr', ← map_inv, ← map_mul, ← map_mul,
        swap_right])
    exact DFunLike.congr_fun h x
  let b : BinaryTetrahedral × BinaryTetrahedral →* E := {
    toFun x := l x.1 * r x.2
    map_one' := by simp
    map_mul' x y := by
      change l (x.1*y.1)*r (x.2*y.2) = (l x.1*r x.2)*(l y.1*r y.2)
      rw [map_mul,map_mul]
      calc
        (l x.1*l y.1)*(r x.2*r y.2) = l x.1*(l y.1*r x.2)*r y.2 := by group
        _ = (l x.1*r x.2)*(l y.1*r y.2) := by rw [(hcomm y.1 x.2).eq]; group }
  let c : C2 →* E := QuaternionGroup.cyclicPowerHom 2 t ht
  have hc1 : c (Multiplicative.ofAdd 1) = t := QuaternionGroup.cyclicPowerHom_one 2 t ht
  have hact (k : C2) : b.comp (swapAction k).toMonoidHom =
      (MulAut.conj (c k)).toMonoidHom.comp b := by
    rcases c2_cases k with rfl | rfl
    · apply MonoidHom.ext
      intro x
      simp
    · apply MonoidHom.ext
      intro x
      change l x.2*r x.1 = c (Multiplicative.ofAdd 1)*(l x.1*r x.2)*(c (Multiplicative.ofAdd 1))⁻¹
      rw [hc1]
      calc
        l x.2*r x.1 = r x.1*l x.2 := (hcomm x.2 x.1).eq
        _ = (t*l x.1*t⁻¹)*(t*r x.2*t⁻¹) := by rw [htl,htr]
        _ = _ := by group
  let s : Wreath →* E := SemidirectProduct.lift b c hact
  refine ⟨s, ?_⟩
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro x
    change f (s (SemidirectProduct.inl x)) = j (SemidirectProduct.inl x)
    rw [SemidirectProduct.lift_inl]
    change f (l x.1*r x.2) = _
    rw [map_mul,hl',hr',← map_mul]
    congr 1
    change SemidirectProduct.inl (x.1,1)*SemidirectProduct.inl (1,x.2) = _
    rw [← map_mul]
    simp
  · apply MonoidHom.ext
    intro k
    change f (s (SemidirectProduct.inr k)) = j (SemidirectProduct.inr k)
    rw [SemidirectProduct.lift_inr]
    rcases c2_cases k with rfl | rfl
    · change f (c 1) = j (SemidirectProduct.inr 1)
      simp
    · rw [hc1,hft]
      rfl

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
