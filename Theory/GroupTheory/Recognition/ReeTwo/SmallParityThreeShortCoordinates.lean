module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeGenerators
public import Theory.SpecificGroups.ReeTwo.CollectedOperations
/-!
# Coordinates for the order-128 rank-three parity candidates

Rows 458, 459, and 460 are parametrized by the cyclic-four coordinate and five
free core bits. Their carrier equations are verified under the collected
polynomial multiplication and inversion. Ordered words in the original seven
generators reconstruct every parameter tuple, proving exact equality with the
specified generator closures and cardinality 128.

The corrected third quotient coordinates give homomorphisms to the binary
three-space. The original basis lifts have the prescribed images, proving
surjectivity in the profile tables' basis convention.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified multiplication
in `CollectedOperations`; the generators and basis positions are those of
`SmallParityThreeGenerators`. Local indices 0, 1, 2 denote global rows 2, 3, 4.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityShort
set_option maxRecDepth 32768
def index : Fin 3 → Fin 6 := ![2,3,4]
abbrev Parameters := FiveFour.Cyclic 4 × (Fin 5 → ZMod 2)
def element (c : Fin 3) (p : Parameters) : SylowModel :=
  let t₀ : ZMod 2 := p.1.toAdd.val
  let t₁ : ZMod 2 := (p.1.toAdd.val / 2 : ℕ)
  ⟨⟨0, 0, 0, p.2 0, p.2 1, if c = 0 then 0 else t₀,
      if c = 0 then p.2 0 else t₀ + t₁ + if c = 2 then p.2 0 else 0,
      p.2 2, p.2 3, p.2 4⟩, p.1⟩
def parameters (x : SylowModel) : Parameters :=
  (x.right, ![x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9])
def carrier (c : Fin 3) (x : SylowModel) : Prop :=
  element c (parameters x) = x
instance (c : Fin 3) (x : SylowModel) : Decidable (carrier c x) :=
  inferInstanceAs (Decidable (_ = _))

def coordinates (c : Fin 3) (x : SylowModel) : SmallParityThreeQuotient :=
  let b := x.left
  let t₀ : ZMod 2 := x.right.toAdd.val
  let t₁ : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd ![b.b3, t₀,
    (![b.b3 + b.b4 + b.b7, t₁ + t₀ * t₁ + b.b7,
       t₁ + t₀ * t₁ + b.b3 + b.b4 + b.b7] : Fin 3 → ZMod 2) c]

theorem parameters_element (c : Fin 3) (p : Parameters) : parameters (element c p) = p := by
  rcases p with ⟨t,w⟩
  apply Prod.ext
  · rfl
  · funext i; fin_cases i <;> rfl

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

private theorem cyclic_cases (t : FiveFour.Cyclic 4) :
    t = Multiplicative.ofAdd (0 : ZMod 4) ∨ t = Multiplicative.ofAdd (1 : ZMod 4) ∨
    t = Multiplicative.ofAdd (2 : ZMod 4) ∨ t = Multiplicative.ofAdd (3 : ZMod 4) :=
  (by decide +kernel : ∀ t : FiveFour.Cyclic 4, t = Multiplicative.ofAdd (0 : ZMod 4) ∨
    t = Multiplicative.ofAdd (1 : ZMod 4) ∨ t = Multiplicative.ofAdd (2 : ZMod 4) ∨
    t = Multiplicative.ofAdd (3 : ZMod 4)) t

set_option maxHeartbeats 8000000 in
theorem carrier_mul (c : Fin 3) (p q : Parameters) :
    carrier c (collectedMul (element c p) (element c q)) := by
  rcases p with ⟨t,w⟩
  rcases q with ⟨s,z⟩
  unfold carrier
  apply SemidirectProduct.ext
  · apply Core.ext
    all_goals first | rfl | skip
    all_goals fin_cases c
    all_goals rcases cyclic_cases t with rfl | rfl | rfl | rfl
    all_goals rcases cyclic_cases s with rfl | rfl | rfl | rfl
    all_goals simp only [element, parameters, collectedMul, collectedAction,
      Function.iterate_succ_apply, Function.iterate_zero_apply, collectedActionStep,
      core_mul_eq, Core.mul, toAdd_ofAdd, ZMod.val_zero,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl]
    all_goals norm_num [Fin.ext_iff,
      show (0 : ZMod 4).val = 0 from rfl, show (1 : ZMod 4).val = 1 from rfl,
      show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl,
      show ((0 : ZMod 4).cast : ZMod 2) = 0 from rfl,
      show ((1 : ZMod 4).cast : ZMod 2) = 1 from rfl,
      show ((2 : ZMod 4).cast : ZMod 2) = 0 from rfl,
      show ((3 : ZMod 4).cast : ZMod 2) = 1 from rfl]
    all_goals try ring_nf
    all_goals reduce_mod_char
    all_goals dsimp [ZMod.cast, ZMod.val]
    all_goals norm_num
    all_goals rfl
  · rfl

set_option maxHeartbeats 8000000 in
theorem carrier_inv : ∀ (c : Fin 3) (p : Parameters),
    carrier c (collectedInv (element c p)) := by decide +kernel

private def carrierSubgroup (c : Fin 3) : Subgroup SylowModel where
  carrier := carrier c
  one_mem' := (by decide +kernel : ∀ c, carrier c 1) c
  mul_mem' := by
    intro x y hx hy
    rw [← hx, ← hy, ← collectedMul_eq]
    exact carrier_mul c _ _
  inv_mem' := by
    intro x hx
    rw [← hx, ← collectedInv_eq]
    exact carrier_inv c _

set_option maxHeartbeats 8000000 in
private theorem generators_carrier : ∀ (c : Fin 3) (j : Fin 9),
    carrier c (smallParityThreeGenerator (index c) j) := by decide +kernel

abbrev Candidate (c : Fin 3) := smallParityTwoCandidate (smallParityThreeIndex (index c))

theorem candidate_carrier (c : Fin 3) (x : SylowModel) (hx : x ∈ Candidate c) :
    carrier c x := by
  have h : Candidate c ≤ carrierSubgroup c := by
    rw [Candidate, smallParityThreeCandidate_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact generators_carrier c j
  exact h hx

private def wordBits (c : Fin 3) (p : Parameters) : Fin 7 → ZMod 2 :=
  let t₀ : ZMod 2 := p.1.toAdd.val
  let t₁ : ZMod 2 := (p.1.toAdd.val / 2 : ℕ)
  let b3 := p.2 0; let b4 := p.2 1; let b7 := p.2 2
  let b8 := p.2 3; let b9 := p.2 4
  ![b3, t₀, t₁, b4,
    (![b3 + b7, t₁ + t₀*t₁ + b7, t₁ + t₀*t₁ + b3 + b7] : Fin 3 → ZMod 2) c,
    (![b3 + b7 + b9, t₀ + t₁ + b4 + t₀*b4 + b7 + b9,
       t₀ + t₁ + b3 + b4 + t₀*b4 + b7 + b9] : Fin 3 → ZMod 2) c,
    (![t₀*b3 + b7 + t₀*b7 + b8, t₁ + t₀*t₁ + b7 + t₀*b7 + b8,
       t₁ + t₀*t₁ + t₀*b3 + b7 + t₀*b7 + b8] : Fin 3 → ZMod 2) c]

private def collectedWord (c : Fin 3) (v : Fin 7 → ZMod 2) : SylowModel :=
  (((List.finRange 7).map fun j =>
    collectedPow (smallParityThreeGenerator (index c) j.castSucc.castSucc) (v j).val)).foldl
      collectedMul 1

private theorem collectedWord_mem (c : Fin 3) (v : Fin 7 → ZMod 2) :
    collectedWord c v ∈ Candidate c := by
  unfold collectedWord
  have hlist : ∀ a ∈ (List.finRange 7).map (fun j =>
      collectedPow (smallParityThreeGenerator (index c) j.castSucc.castSucc) (v j).val),
      a ∈ Candidate c := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rw [collectedPow_eq]
    exact Subgroup.pow_mem _ (smallParityThreeGenerator_mem _ _) _
  generalize (List.finRange 7).map _ = l at hlist ⊢
  have hfold : ∀ a ∈ Candidate c, l.foldl collectedMul a ∈ Candidate c := by
    induction l with
    | nil => intro a ha; exact ha
    | cons x l ih =>
      intro a ha
      apply ih (fun y hy => hlist y (List.mem_cons_of_mem _ hy))
      rw [collectedMul_eq]
      exact Subgroup.mul_mem _ ha (hlist x (List.mem_cons_self))
  exact hfold 1 (Subgroup.one_mem _)

set_option maxHeartbeats 8000000 in
private theorem word_valid : ∀ (c : Fin 3) (p : Parameters),
    collectedWord c (wordBits c p) = element c p := by decide +kernel

theorem element_mem (c : Fin 3) (p : Parameters) : element c p ∈ Candidate c := by
  rw [← word_valid]
  exact collectedWord_mem c _

theorem mem_candidate (c : Fin 3) (x : SylowModel) :
    x ∈ Candidate c ↔ carrier c x := by
  exact ⟨candidate_carrier c x, fun hx => hx ▸ element_mem c (parameters x)⟩

def elementLift (c : Fin 3) (p : Parameters) : Candidate c := ⟨element c p, element_mem c p⟩

def parameterEquiv (c : Fin 3) : Parameters ≃ Candidate c where
  toFun := elementLift c
  invFun x := parameters x.val
  left_inv := parameters_element c
  right_inv x := Subtype.ext (candidate_carrier c x.val x.property)

theorem candidate_card (c : Fin 3) : Nat.card (Candidate c) = 128 := by
  rw [← Nat.card_congr (parameterEquiv c)]
  simp [Parameters, FiveFour.Cyclic]

set_option maxHeartbeats 8000000 in
private theorem coordinates_mul (c : Fin 3) (p q : Parameters) :
    coordinates c (collectedMul (element c p) (element c q)) =
      coordinates c (element c p) * coordinates c (element c q) := by
  rcases p with ⟨t,w⟩
  rcases q with ⟨s,z⟩
  apply Multiplicative.ext
  funext j
  fin_cases c <;> fin_cases j
  all_goals rcases cyclic_cases t with rfl | rfl | rfl | rfl
  all_goals rcases cyclic_cases s with rfl | rfl | rfl | rfl
  all_goals simp only [coordinates, element, collectedMul, collectedAction,
      Function.iterate_succ_apply, Function.iterate_zero_apply, collectedActionStep,
      core_mul_eq, Core.mul, toAdd_mul, Pi.add_apply, toAdd_ofAdd, ZMod.val_zero,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl]
  all_goals norm_num [Fin.ext_iff,
      show (0 : ZMod 4).val = 0 from rfl, show (1 : ZMod 4).val = 1 from rfl,
      show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl,
      show ((0 : ZMod 4).cast : ZMod 2) = 0 from rfl,
      show ((1 : ZMod 4).cast : ZMod 2) = 1 from rfl,
      show ((2 : ZMod 4).cast : ZMod 2) = 0 from rfl,
      show ((3 : ZMod 4).cast : ZMod 2) = 1 from rfl]
  all_goals try ring_nf
  all_goals reduce_mod_char
  all_goals dsimp [ZMod.cast, ZMod.val]
  all_goals norm_num
  all_goals rfl

def projection (c : Fin 3) : Candidate c →* SmallParityThreeQuotient where
  toFun x := coordinates c x.val
  map_one' := (by decide +kernel : ∀ c, coordinates c 1 = 1) c
  map_mul' x y := by
    change coordinates c (x.val * y.val) = coordinates c x.val * coordinates c y.val
    rw [← candidate_carrier c x.val x.property, ← candidate_carrier c y.val y.property,
      ← collectedMul_eq]
    exact coordinates_mul c _ _

set_option maxHeartbeats 8000000 in
theorem projection_basis : ∀ (c : Fin 3) (j : Fin 3),
    projection c (smallParityThreeBasisLift (index c) j) = smallParityThreeBinaryBasis j := by
  decide +kernel

theorem projection_surjective (c : Fin 3) : Function.Surjective (projection c) :=
  smallParityThree_surjective_of_basis _ _ (projection_basis c)

end ReeTwo.SylowModel.SmallParityShort
