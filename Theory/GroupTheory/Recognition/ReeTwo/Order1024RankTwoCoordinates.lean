module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.SpecificGroups.ReeTwo.SylowTailQuotient
public import Theory.Frattini.BinarySquares

/-!
# Coordinates for the rank-two residual Ree two candidates

The original generated subgroups at residual indices 10, 11 and 14 are recovered
as preimages of explicit subgroups of the order-64 tail quotient. Sixteen short
words in their original generators certify the reverse containment. Thus the
coordinate membership equations describe the actual parity-kernel representatives.

Writing `a = t mod 2` and `h = floor(t/2) mod 2`, all three binary projections are
`(b₁ + h, a)`. The membership equations are `b₀ = a` together with, respectively,
`b₂ + b₃ = b₁`, `b₂ + b₃ = b₁ + a`, and `b₂ + b₃ = h + a`.
Their ordered lifts are `(r₁r₃,sr₀)`, `(r₁r₃,sr₀r₃)`, and `(r₁,sr₀r₃)`.
Each fiber has eight free binary coordinates: `h`, `b₂`, and the six tail bits.
This gives explicit fiber equivalences, kernel order 256 and subgroup order 1024.
The Frattini subgroup is contained in each kernel; equality and order counts
remain separate mathematical obligations.

Source: Shinoda (1975), (2.3), pp. 81–82, with the verified multiplication and
root-one convention of `ReeTwo.Sylow` and `SylowTailQuotient`. All finite
certificates are reduced by Lean's kernel. Element formulas are exposed so that
subsequent power and order counts can compute through the actual coordinates.
-/

namespace ReeTwo.SylowModel
open TailQuotient
set_option maxRecDepth 32768

@[expose] public def rankTwoIndex (c : Fin 3) : Fin 15 := ![10,11,14] c
@[expose] public def rankTwoGenerators (c : Fin 3) : Fin 3 → SylowModel :=
  ![![root 2 * root 3, root 1 * root 3, rootOne * root 0],
    ![root 2 * root 3, root 1 * root 3, rootOne * root 0 * root 3],
    ![root 2 * root 3, root 1, rootOne * root 0 * root 3]] c

@[expose] public def rankTwoTailMember (c : Fin 3) (q : TailQuotient.Group) : Prop :=
  let a : ZMod 2 := q.right.toAdd.val
  let h : ZMod 2 := (q.right.toAdd.val / 2 : ℕ)
  q.left.toAdd 0 = a ∧ q.left.toAdd 2 + q.left.toAdd 3 =
    (![q.left.toAdd 1, q.left.toAdd 1 + a, h + a] c)
public instance (c : Fin 3) (q : TailQuotient.Group) : Decidable (rankTwoTailMember c q) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxHeartbeats 8000000 in
public theorem rankTwoTail_closed : ∀ c : Fin 3,
    rankTwoTailMember c 1 ∧
    (∀ x y, rankTwoTailMember c x → rankTwoTailMember c y → rankTwoTailMember c (x*y)) ∧
    (∀ x, rankTwoTailMember c x → rankTwoTailMember c x⁻¹) := by decide +kernel

@[expose] public def rankTwoCoordinates (q : TailQuotient.Group) : OrderProfileQuotient 2 :=
  Multiplicative.ofAdd ![q.left.toAdd 1 + (q.right.toAdd.val / 2 : ℕ),
    (q.right.toAdd.val : ℕ)]

set_option maxHeartbeats 8000000 in
public theorem rankTwoCoordinates_mul : ∀ c : Fin 3,
    rankTwoCoordinates 1 = 1 ∧
    (∀ x y, rankTwoTailMember c x → rankTwoTailMember c y →
      rankTwoCoordinates (x*y) = rankTwoCoordinates x * rankTwoCoordinates y) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
public theorem rankTwoGenerators_tailMember : ∀ c j,
    rankTwoTailMember c (projection (rankTwoGenerators c j)) := by decide +kernel

@[expose] public def rankTwoTailNode (c : Fin 3) : Subgroup TailQuotient.Group where
  carrier := rankTwoTailMember c
  one_mem' := (rankTwoTail_closed c).1
  mul_mem' := (rankTwoTail_closed c).2.1 _ _
  inv_mem' := (rankTwoTail_closed c).2.2 _

@[expose] public def rankTwoWord (c : Fin 3) (p : Fin 4 × Fin 2 × Fin 2) : SylowModel :=
  rankTwoGenerators c 2 ^ p.1.val * rankTwoGenerators c 1 ^ p.2.1.val *
    rankTwoGenerators c 0 ^ p.2.2.val

@[expose] public def rankTwoQuotientWord (c : Fin 3) (p : Fin 4 × Fin 2 × Fin 2) : TailQuotient.Group :=
  projection (rankTwoGenerators c 2) ^ p.1.val * projection (rankTwoGenerators c 1) ^ p.2.1.val *
    projection (rankTwoGenerators c 0) ^ p.2.2.val

public theorem rankTwoWord_projection (c : Fin 3) (p : Fin 4 × Fin 2 × Fin 2) :
    projection (rankTwoWord c p) = rankTwoQuotientWord c p := by
  simp only [rankTwoWord, rankTwoQuotientWord, map_mul, map_pow]

set_option maxHeartbeats 8000000 in
public theorem rankTwoWord_covers : ∀ c q, rankTwoTailMember c q →
    ∃ p : Fin 4 × Fin 2 × Fin 2, projection (rankTwoWord c p) = q := by
  intro c q hq
  have h : ∀ c q, rankTwoTailMember c q →
      ∃ p : Fin 4 × Fin 2 × Fin 2,
        coordinateCode (rankTwoQuotientWord c p) = coordinateCode q := by decide +kernel
  obtain ⟨p, hp⟩ := h c q hq
  exact ⟨p, (rankTwoWord_projection c p).trans (coordinateCode_injective hp)⟩

private theorem reverse_three (a b c : SylowModel) :
    ({a,b,c} : Set SylowModel) = {c,b,a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

set_option maxHeartbeats 8000000 in
public theorem rankTwoCandidate_eq_generated (c : Fin 3) :
    residualCandidate (rankTwoIndex c) = tailSubgroup ⊔
      Subgroup.closure (Set.range (rankTwoGenerators c)) := by
  fin_cases c <;> simp [residualCandidate, rankTwoIndex, rankTwoGenerators]
  all_goals exact congrArg (fun s : Set SylowModel => tailSubgroup ⊔ Subgroup.closure s) (reverse_three _ _ _)

public theorem rankTwoGenerators_mem (c : Fin 3) (j : Fin 3) :
    rankTwoGenerators c j ∈ residualCandidate (rankTwoIndex c) := by
  rw [rankTwoCandidate_eq_generated]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_range_self j))

public theorem rankTwoWord_mem (c : Fin 3) (p : Fin 4 × Fin 2 × Fin 2) :
    rankTwoWord c p ∈ residualCandidate (rankTwoIndex c) :=
  (residualCandidate _).mul_mem
    ((residualCandidate _).mul_mem
      ((residualCandidate _).pow_mem (rankTwoGenerators_mem c 2) _)
      ((residualCandidate _).pow_mem (rankTwoGenerators_mem c 1) _))
    ((residualCandidate _).pow_mem (rankTwoGenerators_mem c 0) _)

public theorem rankTwoCandidate_eq_comap (c : Fin 3) :
    residualCandidate (rankTwoIndex c) = (rankTwoTailNode c).comap projection := by
  apply le_antisymm
  · rw [rankTwoCandidate_eq_generated]
    apply sup_le
    · rw [← ker_projection]
      intro x hx
      change projection x ∈ rankTwoTailNode c
      rw [MonoidHom.mem_ker.mp hx]
      exact (rankTwoTailNode c).one_mem
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact rankTwoGenerators_tailMember c j
  · intro x hx
    obtain ⟨p, hp⟩ := rankTwoWord_covers c (projection x) hx
    have ht : (rankTwoWord c p)⁻¹ * x ∈ tailSubgroup := by
      rw [← ker_projection, MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]
    have h := (residualCandidate _).mul_mem (rankTwoWord_mem c p)
      (tailSubgroup_le_residualCandidate _ ht)
    simpa using h

public theorem rankTwoCandidate_mem (c : Fin 3) (x : SylowModel) :
    x ∈ residualCandidate (rankTwoIndex c) ↔ rankTwoTailMember c (projection x) := by
  rw [rankTwoCandidate_eq_comap]
  rfl

public instance rankTwoCandidate_decidableMem (c : Fin 3) :
    DecidablePred (fun x => x ∈ residualCandidate (rankTwoIndex c)) := fun x =>
  decidable_of_iff (rankTwoTailMember c (projection x)) (rankTwoCandidate_mem c x).symm

@[expose] public def rankTwoProjection (c : Fin 3) :
    residualCandidate (rankTwoIndex c) →* OrderProfileQuotient 2 where
  toFun x := rankTwoCoordinates (projection x.val)
  map_one' := by
    change rankTwoCoordinates (projection 1) = 1
    rw [map_one]
    exact (rankTwoCoordinates_mul c).1
  map_mul' x y := by
    change rankTwoCoordinates (projection (x.val*y.val)) = _
    rw [map_mul]
    exact (rankTwoCoordinates_mul c).2 _ _
      ((rankTwoCandidate_mem c x).mp x.property) ((rankTwoCandidate_mem c y).mp y.property)

@[expose] public def rankTwoRepresentative (c : Fin 3) (v : OrderProfileQuotient 2) :
    residualCandidate (rankTwoIndex c) :=
  ⟨rankTwoGenerators c 1 ^ (v.toAdd 0).val * rankTwoGenerators c 2 ^ (v.toAdd 1).val,
    (residualCandidate _).mul_mem
      ((residualCandidate _).pow_mem (rankTwoGenerators_mem c 1) _)
      ((residualCandidate _).pow_mem (rankTwoGenerators_mem c 2) _)⟩

set_option maxHeartbeats 8000000 in
public theorem rankTwoProjection_representative : ∀ c v,
    rankTwoProjection c (rankTwoRepresentative c v) = v := by decide +kernel

public theorem rankTwoProjection_surjective (c : Fin 3) : Function.Surjective (rankTwoProjection c) :=
  fun v => ⟨rankTwoRepresentative c v, rankTwoProjection_representative c v⟩

public theorem frattini_le_rankTwoProjection_ker (c : Fin 3) :
    frattini (residualCandidate (rankTwoIndex c)) ≤ (rankTwoProjection c).ker := by
  rw [((IsPGroup.of_card (n := 12) card).to_subgroup _).frattini_eq_closure_squares]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  change rankTwoProjection c (x ^ 2) = 1
  rw [map_pow]
  exact (by decide +kernel : ∀ v : OrderProfileQuotient 2, v ^ 2 = 1) _

@[expose] public def rankTwoTailSection (c : Fin 3) (v : OrderProfileQuotient 2)
    (h d : ZMod 2) : TailQuotient.Group :=
  let a := v.toAdd 1
  let b := v.toAdd 0 + h
  ⟨Multiplicative.ofAdd ![a, b, d, d + ![b, b+a, h+a] c],
    Multiplicative.ofAdd ((a.val + 2*h.val : ℕ) : ZMod 4)⟩

set_option maxHeartbeats 8000000 in
public theorem rankTwoTailSection_spec : ∀ c v h d,
    rankTwoTailMember c (rankTwoTailSection c v h d) ∧
    rankTwoCoordinates (rankTwoTailSection c v h d) = v ∧
    (((rankTwoTailSection c v h d).right.toAdd.val / 2 : ℕ) : ZMod 2) = h := by
  decide +kernel

set_option maxHeartbeats 8000000 in
public theorem rankTwoTailSection_recover : ∀ c q, rankTwoTailMember c q →
    rankTwoTailSection c (rankTwoCoordinates q) (q.right.toAdd.val / 2 : ℕ)
      (q.left.toAdd 2) = q := by
  intro c q hq
  apply coordinateCode_injective
  exact (by decide +kernel : ∀ c q, rankTwoTailMember c q →
    coordinateCode (rankTwoTailSection c (rankTwoCoordinates q)
      (q.right.toAdd.val / 2 : ℕ) (q.left.toAdd 2)) = coordinateCode q) c q hq

@[expose] public def rankTwoRawElement (c : Fin 3) (v : OrderProfileQuotient 2) (w : Fin 8 → ZMod 2) : SylowModel :=
  let q := rankTwoTailSection c v (w 0) (w 1)
  ⟨⟨q.left.toAdd 0, q.left.toAdd 1, q.left.toAdd 2, q.left.toAdd 3,
    w 2, w 3, w 4, w 5, w 6, w 7⟩, q.right⟩

private theorem projection_element (c : Fin 3) (v : OrderProfileQuotient 2) (w : Fin 8 → ZMod 2) :
    projection (rankTwoRawElement c v w) = rankTwoTailSection c v (w 0) (w 1) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  · rfl

/-- Eight freely chosen binary coordinates parametrize each rank-two fiber. -/
@[expose] public def rankTwoElement (c : Fin 3) (v : OrderProfileQuotient 2) (w : Fin 8 → ZMod 2) :
    residualCandidate (rankTwoIndex c) :=
  ⟨rankTwoRawElement c v w, (rankTwoCandidate_mem c _).mpr (by
    rw [projection_element]
    exact (rankTwoTailSection_spec c v (w 0) (w 1)).1)⟩

public theorem rankTwoProjection_element (c : Fin 3) (v : OrderProfileQuotient 2)
    (w : Fin 8 → ZMod 2) : rankTwoProjection c (rankTwoElement c v w) = v := by
  change rankTwoCoordinates (projection (rankTwoRawElement c v w)) = v
  rw [projection_element]
  exact (rankTwoTailSection_spec c v (w 0) (w 1)).2.1

@[expose] public def rankTwoRemainder (c : Fin 3) (x : residualCandidate (rankTwoIndex c)) :
    Fin 8 → ZMod 2 :=
  ![(x.val.right.toAdd.val / 2 : ℕ), x.val.left.b2, x.val.left.b4,
    x.val.left.b5, x.val.left.b6, x.val.left.b7, x.val.left.b8, x.val.left.b9]

public theorem rankTwoRemainder_element (c : Fin 3) (v : OrderProfileQuotient 2)
    (w : Fin 8 → ZMod 2) : rankTwoRemainder c (rankTwoElement c v w) = w := by
  funext i
  fin_cases i
  · exact (rankTwoTailSection_spec c v (w 0) (w 1)).2.2
  all_goals rfl

public theorem rankTwoElement_remainder (c : Fin 3) (x : residualCandidate (rankTwoIndex c)) :
    rankTwoElement c (rankTwoProjection c x) (rankTwoRemainder c x) = x := by
  have h := rankTwoTailSection_recover c (projection x.val)
    ((rankTwoCandidate_mem c x.val).mp x.property)
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Core.ext
    · exact congrFun (congrArg (fun q => q.left.toAdd) h) 0
    · exact congrFun (congrArg (fun q => q.left.toAdd) h) 1
    · exact congrFun (congrArg (fun q => q.left.toAdd) h) 2
    · exact congrFun (congrArg (fun q => q.left.toAdd) h) 3
    all_goals rfl
  · exact congrArg (fun q : TailQuotient.Group => q.right) h

@[expose] public def rankTwoFiberEquiv (c : Fin 3) (v : OrderProfileQuotient 2) :
    {x : residualCandidate (rankTwoIndex c) // rankTwoProjection c x = v} ≃ (Fin 8 → ZMod 2) where
  toFun x := rankTwoRemainder c x.val
  invFun w := ⟨rankTwoElement c v w, rankTwoProjection_element c v w⟩
  left_inv x := by
    apply Subtype.ext
    change rankTwoElement c v (rankTwoRemainder c x.val) = x.val
    exact (congrArg (fun v => rankTwoElement c v (rankTwoRemainder c x.val)) x.property.symm).trans
      (rankTwoElement_remainder c x.val)
  right_inv := rankTwoRemainder_element c v

public theorem rankTwoProjection_ker_card (c : Fin 3) : Nat.card (rankTwoProjection c).ker = 256 := by
  change Nat.card {x : residualCandidate (rankTwoIndex c) // rankTwoProjection c x = 1} = 256
  rw [Nat.card_congr (rankTwoFiberEquiv c 1), Nat.card_fun]
  norm_num

/-- The concrete rank-two candidates have order 1024. -/
public theorem rankTwoCandidate_card (c : Fin 3) :
    Nat.card (residualCandidate (rankTwoIndex c)) = 1024 := by
  have hi : (rankTwoProjection c).ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (rankTwoProjection_surjective c)]
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card (Fin 2 → ZMod 2) = 4
    rw [Nat.card_fun]
    norm_num
  have h := (rankTwoProjection c).ker.index_mul_card
  rw [hi, rankTwoProjection_ker_card] at h
  exact h.symm

/-- The prescribed order-one, order-two and order-four counts in the ordered basis.
This table specifies the remaining count obligation; it does not assert it. -/
@[expose] public def rankTwoProfileCounts (c : Fin 3) (v : OrderProfileQuotient 2) : ℕ × ℕ × ℕ :=
  if v.toAdd 1 = 0 then
    if v.toAdd 0 = 0 then (1,47,80)
    else if c = 2 then (0,0,256) else (0,32,224)
  else (0,0,0)

end ReeTwo.SylowModel
