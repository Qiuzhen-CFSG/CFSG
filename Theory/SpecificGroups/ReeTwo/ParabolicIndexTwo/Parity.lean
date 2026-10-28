module

public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Derived
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# The dihedral parity quotient and the parity-core lattice

The literal even-coordinate subgroup of the faithful five-by-four complement
is identified with `DihedralGroup 5`. Rotations retain the cyclic-five
coordinate, and the dihedral reflection is the square of the cyclic-four
generator. Composing with the compatible parity quotient map preserves both
the specified five-element and an explicit even reflection representative.
Every Sylow two-subgroup of this quotient is cyclic of order two; those of
the core-character and mixed-character quotients are cyclic of order four.

Inside the parity kernel let Q be its intrinsic two-core, E = [Q,Q],
F = C_H(E), and W the embedded first omega subgroup of the coordinate core.
Transport through the actual core inclusion gives E < W < Q, W ∩ F = E,
and W ∨ F = Q, with respective orders 32, 512, 1024, and 64. The existing
`parity_pCore_card` and `parity_centralizer_derived_card` supply the last two
orders. E, F, and W are characteristic in the local group and in Q;
furthermore E is characteristic in W and is the first omega subgroup of F.
The additional invariant subgroup W is retained in the local calculation.

The proof uses the computed core lattice in `CoreParabolicOmega`, the omega
commutators in `CoreOmegaDerived`, and the intrinsic inclusion and centralizer
exports from `ParabolicIndexTwo.Derived`. These are concrete local-model
results for the index-two alternatives; ambient identifications, quotient
actions and involution fusion are separate calculations.

Sources: Aschbacher--Smith, quasithin Lemma 14.2.21, printed p.989;
Aschbacher, *The Tits group as a standard subgroup* (1982), Section 3;
Parrott, *A characterization of the Tits' simple group* (1972), printed p.672.
Parrott's quotient is the order-twenty Frobenius group: the order-ten parity
quotient is kept as its own concrete alternative.
-/

public section
open Subgroup
namespace ReeTwo.Centralizer.IndexTwo

private def dihedralCoordinates : DihedralGroup 5 → FiveFour.Group
  | .r i => SemidirectProduct.inl (Multiplicative.ofAdd i)
  | .sr i => FiveFour.a ^ 2 * SemidirectProduct.inl (Multiplicative.ofAdd i)

/-- The coordinate embedding sends the dihedral reflection to the even four-coordinate. -/
def parityDihedralEmbedding : DihedralGroup 5 →* parityComplement where
  toFun x := ⟨dihedralCoordinates x, (by decide +kernel :
    ∀ x, parityComplementCharacter (dihedralCoordinates x) = 1) x⟩
  map_one' := by decide +kernel
  map_mul' := by
    intro x y
    apply Subtype.ext
    exact (by decide +kernel : ∀ x y,
      dihedralCoordinates (x * y) = dihedralCoordinates x * dihedralCoordinates y) x y

private def parityDihedralInverse (x : parityComplement) : DihedralGroup 5 :=
  if x.val.right = 1 then .r x.val.left.toAdd else .sr (-x.val.left.toAdd)

/-- The even-coordinate complement is dihedral, with explicit inverse coordinates. -/
def parityComplementDihedralEquiv : parityComplement ≃* DihedralGroup 5 :=
  ({ parityDihedralEmbedding with
    invFun := parityDihedralInverse
    left_inv := by decide +kernel
    right_inv := by decide +kernel } : DihedralGroup 5 ≃* parityComplement).symm

/-- The inverse equivalence is the specified coordinate embedding. -/
@[simp] theorem parityComplementDihedralEquiv_symm_apply (x : DihedralGroup 5) :
    parityComplementDihedralEquiv.symm x = parityDihedralEmbedding x := (rfl)

/-- The embedding retains every cyclic-five rotation coordinate. -/
@[simp] theorem parityDihedralEmbedding_rotation (i : ZMod 5) :
    (parityDihedralEmbedding (.r i) : FiveFour.Group) =
      SemidirectProduct.inl (Multiplicative.ofAdd i) := (rfl)

/-- The reflection is the square of the specified cyclic-four generator. -/
@[simp] theorem parityDihedralEmbedding_reflection :
    (parityDihedralEmbedding (.sr 0) : FiveFour.Group) = FiveFour.a ^ 2 := by
  decide +kernel

/-- The inverse coordinate identification recovers the specified rotations. -/
@[simp] theorem parityComplementDihedralEquiv_rotation (i : ZMod 5) :
    parityComplementDihedralEquiv (parityDihedralEmbedding (.r i)) = .r i :=
  parityComplementDihedralEquiv.apply_symm_apply _

/-- The even cyclic-four element gives the standard dihedral reflection. -/
@[simp] theorem parityComplementDihedralEquiv_reflection :
    parityComplementDihedralEquiv (parityDihedralEmbedding (.sr 0)) = .sr 0 :=
  parityComplementDihedralEquiv.apply_symm_apply _

/-- The actual parity two-core quotient, with its marked dihedral identification. -/
@[expose] noncomputable def parityQuotientDihedralEquiv :
    (parityLocal ⧸ pCore 2 parityLocal) ≃* DihedralGroup 5 :=
  parityQuotientEquiv.trans parityComplementDihedralEquiv

/-- The dihedral quotient equivalence retains projection on representatives. -/
@[simp] theorem parityQuotientDihedralEquiv_mk (x : parityLocal) :
    parityQuotientDihedralEquiv (QuotientGroup.mk' _ x) =
      parityComplementDihedralEquiv (parityProjection x) := rfl

/-- The specified five-element becomes the standard dihedral rotation. -/
@[simp] theorem parityQuotientDihedralEquiv_five :
    parityQuotientDihedralEquiv
      (QuotientGroup.mk' _ ⟨fiveGenerator, character_fiveGenerator⟩) = .r 1 := by
  rw [parityQuotientDihedralEquiv_mk]
  apply parityComplementDihedralEquiv.symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact projection_fiveGenerator

/-- The even cyclic-four reflection lifted through the actual complement inclusion. -/
@[expose] noncomputable def parityReflection : parityLocal :=
  ⟨SemidirectProduct.inr (Core.complementEquiv (FiveFour.a ^ 2)), by
    change parityComplementCharacter (Core.complementEquiv.symm
      (Core.complementEquiv (FiveFour.a ^ 2))) = 1
    rw [Core.complementEquiv.symm_apply_apply]
    decide +kernel⟩

/-- The chosen local reflection projects to the standard dihedral reflection. -/
@[simp] theorem parityQuotientDihedralEquiv_reflection :
    parityQuotientDihedralEquiv (QuotientGroup.mk' _ parityReflection) = .sr 0 := by
  rw [parityQuotientDihedralEquiv_mk]
  apply parityComplementDihedralEquiv.symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change projection (SemidirectProduct.inr (Core.complementEquiv (FiveFour.a ^ 2))) =
    (parityDihedralEmbedding (.sr 0) : FiveFour.Group)
  rw [projection_inr, Core.complementEquiv.symm_apply_apply, parityDihedralEmbedding_reflection]

private theorem fourComplement_card :
    Nat.card (SemidirectProduct.inr : FiveFour.Cyclic 4 →* FiveFour.Group).range = 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inr_injective).toEquiv]
  change Nat.card (ZMod 4) = 4
  simp

/-- The specified cyclic-four complement is a Sylow two-subgroup. -/
@[expose] noncomputable def fiveFourSylowTwo : Sylow 2 FiveFour.Group :=
  Sylow.ofCard (SemidirectProduct.inr : FiveFour.Cyclic 4 →* FiveFour.Group).range (by
    rw [fourComplement_card, FiveFour.card,
      show 20 = 2 ^ 2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, (by decide : Nat.Prime 5).factorization])

/-- Every Sylow two-subgroup of the faithful five-by-four group is cyclic. -/
theorem fiveFour_sylowTwo_cyclic (T : Sylow 2 FiveFour.Group) : IsCyclic T := by
  let e := MonoidHom.ofInjective
    (SemidirectProduct.inr_injective (φ := FiveFour.action))
  let : IsCyclic fiveFourSylowTwo := isCyclic_of_surjective e e.surjective
  exact isCyclic_of_injective (T.equiv fiveFourSylowTwo).toMonoidHom
    (T.equiv fiveFourSylowTwo).injective

/-- Every Sylow two-subgroup of the parity two-core quotient has order two. -/
theorem parity_sylowTwo_card (T : Sylow 2 (parityLocal ⧸ pCore 2 parityLocal)) :
    Nat.card T = 2 := by
  rw [T.card_eq_multiplicity, parity_quotient_card,
    show 10 = 2 * 5 from rfl, Nat.factorization_mul (by decide) (by decide)]
  norm_num [Nat.prime_two.factorization, (by decide : Nat.Prime 5).factorization]

/-- Every Sylow two-subgroup of the parity two-core quotient is cyclic. -/
theorem parity_sylowTwo_cyclic (T : Sylow 2 (parityLocal ⧸ pCore 2 parityLocal)) :
    IsCyclic T := isCyclic_of_prime_card (parity_sylowTwo_card T)

/-- The core-character and mixed-character quotients have Sylow two-subgroups of order four. -/
theorem alternative_sylowTwo_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (T : Sylow 2 (χ.ker ⧸ pCore 2 χ.ker)) : Nat.card T = 4 := by
  rw [T.card_eq_multiplicity, alternative_quotient_card χ hχ,
    show 20 = 2 ^ 2 * 5 from rfl,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, (by decide : Nat.Prime 5).factorization]

/-- Both alternative quotients have cyclic Sylow two-subgroups, via their actual quotient equivalences. -/
theorem alternative_sylowTwo_cyclic (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (T : Sylow 2 (χ.ker ⧸ pCore 2 χ.ker)) : IsCyclic T := by
  let e := alternativeQuotientEquiv χ hχ
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsCyclic S := fiveFour_sylowTwo_cyclic S
  let f : T ≃* S := T.toSubgroup.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_injective f.toMonoidHom f.injective

/-- The intrinsic two-core of the parity local group, of order 1024. -/
noncomputable abbrev parityQ : Subgroup parityLocal := pCore 2 parityLocal
/-- The derived subgroup of the intrinsic parity two-core. -/
noncomputable abbrev parityE : Subgroup parityLocal := ⁅parityQ, parityQ⁆
/-- The centralizer of the derived subgroup in the whole parity local group. -/
noncomputable abbrev parityF : Subgroup parityLocal := centralizer (parityE : Set parityLocal)
/-- The literal embedded first omega subgroup, restricted to the parity local group. -/
@[expose] noncomputable def parityW : Subgroup parityLocal := omega.subgroupOf parityLocal

private theorem parityCoreInclusion_map (A : Subgroup Core) :
    A.map parityCoreInclusion =
      (A.map (SemidirectProduct.inl : Core →* Centralizer)).subgroupOf parityLocal := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,he⟩
    exact ⟨y,hy,Subtype.ext he⟩

/-- The actual core inclusion carries the coordinate derived tail onto E. -/
theorem parityCoreInclusion_map_derived :
    (commutator Core).map parityCoreInclusion = parityE := by
  rw [parityE, parityQ, parityCoreInclusion_map, parity_derived]
  rfl

/-- The actual core inclusion carries the coordinate omega subgroup onto W. -/
theorem parityCoreInclusion_map_omega :
    (omega₁ Core (p := 2)).map parityCoreInclusion = parityW :=
  parityCoreInclusion_map _

/-- The coordinate derived centralizer maps onto the whole local derived centralizer F. -/
theorem parityCoreInclusion_map_centralizer :
    (centralizer (commutator Core : Set Core)).map parityCoreInclusion = parityF := by
  rw [parityF, parityE, parityQ, parityCoreInclusion_map,
    parity_centralizer_derived, centralizer_derived_eq_map]

private theorem parityCoreInclusion_map_top :
    (⊤ : Subgroup Core).map parityCoreInclusion = parityQ := by
  rw [← MonoidHom.range_eq_map, parityCoreInclusion_range]

/-- W is the image of the intrinsic first omega subgroup of Q. -/
theorem parityW_eq_intrinsic_omega :
    parityW = (omega₁ parityQ (p := 2)).map parityQ.subtype := by
  rw [← parityCoreInclusion_map_omega]
  exact Subgroup.map_omega_eq_of_injective_of_range_eq
    parityCoreInclusion parityQ.subtype parityCoreInclusion_injective parityQ.subtype_injective
    (by rw [parityCoreInclusion_range, Subgroup.range_subtype]) 2 1

/-- W is characteristic in the whole parity local group. -/
theorem parityW_characteristic : parityW.Characteristic := by
  rw [parityW_eq_intrinsic_omega]
  let : (omega₁ parityQ (p := 2)).Characteristic := omega₁_characteristic _
  infer_instance

/-- E is characteristic in the whole parity local group. -/
theorem parityE_characteristic : parityE.Characteristic := by infer_instance

/-- F is characteristic in the whole parity local group. -/
theorem parityF_characteristic : parityF.Characteristic := by infer_instance

/-- The parity derived subgroup is strictly smaller than its embedded omega subgroup. -/
theorem parityE_lt_parityW : parityE < parityW := by
  rw [← parityCoreInclusion_map_derived, ← parityCoreInclusion_map_omega]
  exact lt_of_le_of_ne (Subgroup.map_mono Core.derived_lt_omega.le)
    (fun h => Core.derived_lt_omega.ne (Subgroup.map_injective parityCoreInclusion_injective h))

/-- The embedded omega subgroup is proper in the parity two-core. -/
theorem parityW_lt_parityQ : parityW < parityQ := by
  rw [← parityCoreInclusion_map_omega, ← parityCoreInclusion_map_top]
  exact lt_of_le_of_ne (Subgroup.map_mono Core.omega_lt_top.le)
    (fun h => Core.omega_lt_top.ne (Subgroup.map_injective parityCoreInclusion_injective h))

/-- The embedded omega subgroup intersects the local derived centralizer precisely in E. -/
theorem parityW_inf_parityF : parityW ⊓ parityF = parityE := by
  rw [← parityCoreInclusion_map_omega, ← parityCoreInclusion_map_centralizer,
    ← Subgroup.map_inf _ _ _ parityCoreInclusion_injective,
    Core.omega_inf_centralizer_derived, parityCoreInclusion_map_derived]

/-- The embedded omega subgroup and the local derived centralizer generate Q. -/
theorem parityW_sup_parityF : parityW ⊔ parityF = parityQ := by
  rw [← parityCoreInclusion_map_omega, ← parityCoreInclusion_map_centralizer,
    ← Subgroup.map_sup, Core.omega_sup_centralizer_derived, parityCoreInclusion_map_top]

/-- The whole local derived centralizer lies inside the parity two-core. -/
theorem parityF_le_parityQ : parityF ≤ parityQ := by
  rw [← parityW_sup_parityF]
  exact le_sup_right

/-- The parity derived subgroup has order 32. -/
theorem parityE_card : Nat.card parityE = 32 := by
  rw [← parityCoreInclusion_map_derived,
    ← Nat.card_congr ((commutator Core).equivMapOfInjective
      parityCoreInclusion parityCoreInclusion_injective).toEquiv]
  exact Core.derived_card

/-- The embedded omega subgroup in the parity kernel has order 512. -/
theorem parityW_card : Nat.card parityW = 512 := by
  rw [← parityCoreInclusion_map_omega,
    ← Nat.card_congr ((omega₁ Core (p := 2)).equivMapOfInjective
      parityCoreInclusion parityCoreInclusion_injective).toEquiv]
  exact Core.omega_card

/-- The parity derived subgroup is elementary abelian. -/
theorem parityE_elementary : IsElementaryAbelian 2 parityE := by
  rw [← parityCoreInclusion_map_derived]
  let : IsElementaryAbelian 2 (commutator Core) := Core.derived_elementary
  exact IsElementaryAbelian.map _

/-- The embedded omega subgroup has exactly the same derived tail E. -/
theorem parityW_commutator : ⁅parityW, parityW⁆ = parityE := by
  rw [← parityCoreInclusion_map_omega, ← Subgroup.map_commutator,
    Core.omega_commutator, parityCoreInclusion_map_derived]

/-- E is characteristic inside W as its intrinsic derived subgroup. -/
theorem parityE_characteristic_in_parityW : (parityE.subgroupOf parityW).Characteristic := by
  have he : commutator parityW = parityE.subgroupOf parityW := by
    apply Subgroup.map_injective parityW.subtype_injective
    rw [Subgroup.map_subtype_commutator, parityW_commutator,
      Subgroup.map_subgroupOf_eq_of_le parityE_lt_parityW.le]
  rw [← he]
  infer_instance

/-- The derived subgroup lies in its centralizer. -/
theorem parityE_le_parityF : parityE ≤ parityF := by
  rw [← parityW_inf_parityF]
  exact inf_le_right

/-- The intrinsic first omega subgroup of F has image E in the parity local group. -/
theorem parityF_omega_map :
    (omega₁ parityF (p := 2)).map parityF.subtype = parityE := by
  let C := centralizer (commutator Core : Set Core)
  have h := Subgroup.map_omega_eq_of_injective_of_range_eq
    (parityCoreInclusion.comp C.subtype) parityF.subtype
    (parityCoreInclusion_injective.comp C.subtype_injective) parityF.subtype_injective
    (by rw [MonoidHom.range_comp, Subgroup.range_subtype,
      parityCoreInclusion_map_centralizer, Subgroup.range_subtype]) 2 1
  rw [← h, ← Subgroup.map_map, Core.centralizer_omega_map_eq_derived,
    parityCoreInclusion_map_derived]

/-- Inside F, the subgroup E is exactly its intrinsic first omega subgroup. -/
theorem parityF_omega : omega₁ parityF (p := 2) = parityE.subgroupOf parityF := by
  apply Subgroup.map_injective parityF.subtype_injective
  rw [parityF_omega_map, Subgroup.map_subgroupOf_eq_of_le parityE_le_parityF]

/-- E is characteristic in F as its first omega subgroup. -/
theorem parityE_characteristic_in_parityF : (parityE.subgroupOf parityF).Characteristic := by
  rw [← parityF_omega]
  exact omega₁_characteristic _

/-- Restricting E to Q gives the intrinsic derived subgroup of Q. -/
theorem parityE_subgroupOf_parityQ : parityE.subgroupOf parityQ = commutator parityQ := by
  apply Subgroup.map_injective parityQ.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (parityE_lt_parityW.le.trans parityW_lt_parityQ.le),
    Subgroup.map_subtype_commutator]

/-- E is characteristic in the intrinsic two-core Q. -/
theorem parityE_characteristic_in_parityQ : (parityE.subgroupOf parityQ).Characteristic := by
  rw [parityE_subgroupOf_parityQ]
  infer_instance

/-- Restricting W to Q gives the intrinsic first omega subgroup of Q. -/
theorem parityW_subgroupOf_parityQ : parityW.subgroupOf parityQ = omega₁ parityQ (p := 2) := by
  apply Subgroup.map_injective parityQ.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le parityW_lt_parityQ.le, parityW_eq_intrinsic_omega]

/-- W is characteristic in the intrinsic two-core Q. -/
theorem parityW_characteristic_in_parityQ : (parityW.subgroupOf parityQ).Characteristic := by
  rw [parityW_subgroupOf_parityQ]
  exact omega₁_characteristic _

/-- Restricting F to Q gives the intrinsic derived centralizer in Q. -/
theorem parityF_subgroupOf_parityQ : parityF.subgroupOf parityQ =
    centralizer (commutator parityQ : Set parityQ) := by
  rw [← parityE_subgroupOf_parityQ]
  ext x
  constructor
  · intro hx y hy
    exact Subtype.ext (hx (y : parityLocal) hy)
  · intro hx y hy
    exact congrArg Subtype.val
      (hx ⟨y, parityE_lt_parityW.le.trans parityW_lt_parityQ.le hy⟩ hy)

/-- F is characteristic in the intrinsic two-core Q. -/
theorem parityF_characteristic_in_parityQ : (parityF.subgroupOf parityQ).Characteristic := by
  rw [parityF_subgroupOf_parityQ]
  infer_instance

end ReeTwo.Centralizer.IndexTwo
