module

public import Theory.SpecificGroups.ReeTwo.SylowTailCoordinates

/-!
# A computable order-64 quotient of the Ree two Sylow model

The first four binary core coordinates form an elementary abelian group.
Right conjugation by root 1 acts by the unipotent map
`(a,b,c,d) ↦ (a,b+a,c+a+b,d+b)`. Its fourth power is the identity.
The resulting semidirect product with the cyclic-four factor is the quotient
by the last six roots. Compatibility is checked on the ten core generators,
so the projection is a homomorphism on the full Sylow group.

The explicit section supplies lifts for quotient computations. The kernel,
cardinality and subgroup correspondence lemmas reduce every order-1024
subgroup to an order-16 subgroup of this computable group; no centricity
assumption is needed for this reduction.

Source: Shinoda (1975), (2.3), pp. 81–82, with the multiplication and action
conventions verified in `ReeTwo.Core` and `ReeTwo.RootAction`.
-/

@[expose] public section
namespace ReeTwo
namespace TailQuotient
abbrev Vector := Multiplicative (Fin 4 → ZMod 2)
def shift (v : Vector) : Vector :=
  Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 1 + v.toAdd 0,
    v.toAdd 2 + v.toAdd 0 + v.toAdd 1, v.toAdd 3 + v.toAdd 1]
def shiftAut : MulAut Vector where
  toFun := shift
  invFun v := shift (shift (shift v))
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
theorem shiftAut_four : shiftAut ^ 4 = 1 := by
  ext v i
  exact congrFun (congrArg Multiplicative.toAdd
    ((by decide +kernel : ∀ v : Vector, (shiftAut ^ 4) v = v) v)) i
def action : FiveFour.Cyclic 4 →* MulAut Vector :=
  FiveFour.cyclicHom shiftAut shiftAut_four
abbrev Group := Vector ⋊[action] FiveFour.Cyclic 4
instance : Fintype Group := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem compatible (t : FiveFour.Cyclic 4) :
    Core.leadingFour.comp ((Core.complementAction.comp SemidirectProduct.inr) t).toMonoidHom =
    (action t).toMonoidHom.comp Core.leadingFour := by
  apply Core.hom_ext
  intro i
  exact (by decide +kernel : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot),
    Core.leadingFour ((Core.complementAction.comp SemidirectProduct.inr) t (Core.root i)) =
    action t (Core.leadingFour (Core.root i))) t i
def projection : SylowModel →* Group :=
  SemidirectProduct.map Core.leadingFour (MonoidHom.id _) compatible
def lift (q : Group) : SylowModel :=
  ⟨⟨q.left.toAdd 0, q.left.toAdd 1, q.left.toAdd 2, q.left.toAdd 3, 0, 0, 0, 0, 0, 0⟩,
    q.right⟩
theorem projection_lift (q : Group) : projection (lift q) = q := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  · rfl
theorem projection_surjective : Function.Surjective projection :=
  fun q => ⟨lift q, projection_lift q⟩
theorem ker_projection : projection.ker = SylowModel.tailSubgroup := by
  ext x
  rw [SylowModel.mem_tailSubgroup]
  change projection x = 1 ↔ _
  constructor
  · intro h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    exact ⟨hr, (Core.mem_leadingFour_ker _).mp hl⟩
  · rintro ⟨hr, hl⟩
    exact SemidirectProduct.ext ((Core.mem_leadingFour_ker _).mpr hl) hr
theorem card : Nat.card Group = 64 := by
  rw [SemidirectProduct.card]
  change Nat.card (Fin 4 → ZMod 2) * Nat.card (ZMod 4) = 64
  simp

/-- Encode the four binary coordinates followed by the cyclic-four coordinate. -/
def coordinateCode (q : Group) : ℕ :=
  (q.left.toAdd 0).val + 2 * (q.left.toAdd 1).val +
    4 * (q.left.toAdd 2).val + 8 * (q.left.toAdd 3).val + 16 * q.right.toAdd.val

/-- Decode a coordinate code; coordinates are reduced modulo two and four. -/
def coordinateElement (n : ℕ) : Group :=
  ⟨Multiplicative.ofAdd ![(n : ZMod 2), ((n / 2 : ℕ) : ZMod 2),
    ((n / 4 : ℕ) : ZMod 2), ((n / 8 : ℕ) : ZMod 2)],
    Multiplicative.ofAdd ((n / 16 : ℕ) : ZMod 4)⟩

theorem coordinateElement_code : ∀ q : Group,
    coordinateElement (coordinateCode q) = q := by
  intro q
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    exact (by decide +kernel : ∀ (q : Group) (i : Fin 4),
      (coordinateElement (coordinateCode q)).left.toAdd i = q.left.toAdd i) q i
  · exact (by decide +kernel : ∀ q : Group,
      (coordinateElement (coordinateCode q)).right = q.right) q

theorem coordinateCode_element : ∀ n : Fin 64,
    coordinateCode (coordinateElement n.val) = n.val := by decide +kernel

/-- Equality can be checked on the integer coordinate encoding. -/
theorem coordinateCode_injective : Function.Injective coordinateCode := by
  intro x y h
  rw [← coordinateElement_code x, ← coordinateElement_code y, h]

/-- Subgroups containing the tail are recovered exactly from their image. -/
theorem comap_map (U : Subgroup SylowModel) (hU : SylowModel.tailSubgroup ≤ U) :
    (U.map projection).comap projection = U :=
  Subgroup.comap_map_eq_self (ker_projection ▸ hU)

/-- Conjugation commutes with projection. -/
theorem map_conjugate (U : Subgroup SylowModel) (g : SylowModel) :
    (U.map (MulAut.conj g).toMonoidHom).map projection =
      (U.map projection).map (MulAut.conj (projection g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change projection (g * x * g⁻¹) = projection g * projection x * (projection g)⁻¹
  simp only [map_mul, map_inv]

end TailQuotient
namespace SylowModel

/-- An order-1024 subgroup of the Sylow model has index four. -/
theorem index_eq_four_of_card (U : Subgroup SylowModel) (hU : Nat.card U = 1024) :
    U.index = 4 := by
  have h := U.index_mul_card
  rw [hU, card] at h
  omega

/-- All order-1024 subgroups contain the tail, including parity-kernel cases. -/
theorem tailSubgroup_le_of_card (U : Subgroup SylowModel) (hU : Nat.card U = 1024) :
    tailSubgroup ≤ U := tailSubgroup_le_of_index_eq_four U (index_eq_four_of_card U hU)

/-- The image of an order-1024 subgroup has order sixteen. -/
theorem tailQuotient_image_card (U : Subgroup SylowModel) (hU : Nat.card U = 1024) :
    Nat.card (U.map TailQuotient.projection) = 16 := by
  have hi := U.index_map_eq TailQuotient.projection_surjective
    (TailQuotient.ker_projection ▸ tailSubgroup_le_of_card U hU)
  rw [index_eq_four_of_card U hU] at hi
  have h := (U.map TailQuotient.projection).index_mul_card
  rw [hi, TailQuotient.card] at h
  omega

end SylowModel
end ReeTwo
