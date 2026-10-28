module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.ConstructionInputs

/-!
# The reflection in the placed local A₅

The prescribed graph action is nontrivial. Simplicity of the actual subgroup
makes its action on the literal U-fixed space injective, so its graph
reflection has order two. This needs no faithfulness assertion for the whole
tetrahedral centralizer. A₅ fusion then conjugates the specified involution
to this reflection in the actual Leech quotient.

The graph exchanges the three coordinate pairs (0,5), (1,3), (2,4).
Its fixed vectors are therefore parametrized by three GF(4) coordinates:
there are 64, giving binary dimension six. The fusion assembly uses this
invariant to distinguish possible integral lifts. No Conway class is yet
identified here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four class in Lemma 47.2, p.261.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
variable {L : LongFrame}

/-- The actual subgroup action on the binary U-fixed space. -/
def A5Placement.fixedAction (P : A5Placement L) :
    P.subgroup →* (fixedSpace ≃ₗ[Bit] fixedSpace) where
  toFun a :=
    { toFun := fun v => ⟨quotientModTwoRepresentation a.val v.val,
        centralizerI_preserves_fixedSpace (P.le_centralizer a.property).1 v.property⟩
      invFun := fun v => ⟨quotientModTwoRepresentation a.val⁻¹ v.val,
        centralizerI_preserves_fixedSpace
          (centralizerI.inv_mem (P.le_centralizer a.property).1) v.property⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp
      map_add' := by intro v w; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c v; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by ext v; exact congrArg (fun f => f v.val) (map_one quotientModTwoRepresentation)
  map_mul' := by
    intro a b
    ext v
    exact congrArg (fun f => f v.val) (map_mul quotientModTwoRepresentation a.val b.val)

private theorem A5Placement.reflection_action_ne_one (P : A5Placement L) :
    P.fixedAction P.reflection ≠ 1 := by
  intro h
  let v : fixedSpace := ⟨L.coordinates (Pi.single 0 1),
    (L.coordinates_range _).mpr ⟨_, rfl⟩⟩
  have he := congrArg (fun f : fixedSpace ≃ₗ[Bit] fixedSpace => (f v).val) h
  change quotientModTwoRepresentation (P.reflection : LeechCentralQuotient)
    (L.coordinates (Pi.single 0 1)) = L.coordinates (Pi.single 0 1) at he
  rw [P.reflection_action] at he
  have hv := congrFun (L.coordinates_injective he) 0
  norm_num [pairRepresentation, pairLinear, pairAction, flip, Pi.single_apply] at hv
  exact (by decide : (5 : Fin 6) ≠ 0) hv

/-- Simplicity gives faithfulness for this A₅ alone. -/
theorem A5Placement.fixedAction_injective (P : A5Placement L) :
    Function.Injective P.fixedAction := by
  let : IsSimpleGroup P.subgroup := P.alternating.isSimpleGroup
  rcases P.fixedAction.normal_ker.eq_bot_or_eq_top with h | h
  · exact P.fixedAction.ker_eq_bot_iff.mp h
  · have hr : P.reflection ∈ P.fixedAction.ker := h ▸ Subgroup.mem_top _
    exact False.elim (P.reflection_action_ne_one (MonoidHom.mem_ker.mp hr))

theorem A5Placement.reflection_sq (P : A5Placement L) : P.reflection ^ 2 = 1 := by
  apply P.fixedAction_injective
  rw [map_pow, map_one, pow_two]
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  obtain ⟨w, hw⟩ := (L.coordinates_range v.val).mp v.property
  change quotientModTwoRepresentation (P.reflection : LeechCentralQuotient)
    (quotientModTwoRepresentation (P.reflection : LeechCentralQuotient) v.val) = v.val
  rw [← hw, P.reflection_action, P.reflection_action]
  congr 1
  funext i
  fin_cases i <;> simp [pairRepresentation, pairLinear, pairAction, flip]

theorem A5Placement.reflection_order (P : A5Placement L) : orderOf P.reflection = 2 :=
  orderOf_eq_prime P.reflection_sq (by
    intro h
    exact P.reflection_action_ne_one (h ▸ map_one P.fixedAction))

/-- Fusion inside the actual A₅ supplies the ambient conjugacy. -/
theorem A5Placement.involution_isConj_reflection (P : A5Placement L) :
    IsConj (P.involution : LeechCentralQuotient) (P.reflection : LeechCentralQuotient) := by
  have h := alternatingGroup.five_involutions_isConj
    (P.alternating P.involution) (P.alternating P.reflection)
    (by rw [P.alternating.orderOf_eq, P.involution_order])
    (by rw [P.alternating.orderOf_eq, P.reflection_order])
  have hi := P.alternating.symm.toMonoidHom.map_isConj h
  have h' : IsConj P.involution P.reflection := by
    change IsConj (P.alternating.symm (P.alternating P.involution))
      (P.alternating.symm (P.alternating P.reflection)) at hi
    simpa only [MulEquiv.symm_apply_apply] using hi
  exact P.subgroup.subtype.map_isConj h'

/-- Fixed vectors of the reflection within the published U-fixed space. -/
def A5Placement.reflectionFixedSpace (P : A5Placement L) : Submodule Bit LeechModTwo :=
  fixedSpace ⊓ LinearMap.ker (difference (P.reflection : LeechCentralQuotient))

private def tripleDouble (w : Fin 3 → F) : Fin 6 → F :=
  ![w 0,w 1,w 2,w 1,w 2,w 0]

private theorem tripleDouble_fixed (w : Fin 3 → F) :
    pairRepresentation (flip, flip) (tripleDouble w) = tripleDouble w := by
  funext i
  fin_cases i <;> simp [tripleDouble, pairRepresentation, pairLinear, pairAction, flip]

theorem A5Placement.reflectionFixedSpace_card (P : A5Placement L) :
    Nat.card P.reflectionFixedSpace = 64 := by
  let f : (Fin 3 → F) → P.reflectionFixedSpace := fun w =>
    ⟨L.coordinates (tripleDouble w),
      (L.coordinates_range _).mpr ⟨_, rfl⟩, by
        change quotientModTwoRepresentation (P.reflection : LeechCentralQuotient)
          (L.coordinates (tripleDouble w)) - L.coordinates (tripleDouble w) = 0
        rw [P.reflection_action, tripleDouble_fixed, sub_self]⟩
  have hi : Function.Injective f := by
    intro v w h
    have he := L.coordinates_injective (congrArg Subtype.val h)
    funext i
    fin_cases i
    · exact congrFun he 0
    · exact congrFun he 1
    · exact congrFun he 2
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨w, hw⟩ := (L.coordinates_range v.val).mp v.property.1
    have hfix := v.property.2
    change quotientModTwoRepresentation (P.reflection : LeechCentralQuotient) v.val - v.val = 0 at hfix
    rw [← hw, P.reflection_action, sub_eq_zero] at hfix
    have he := L.coordinates_injective hfix
    have h3 : w 1 = w 3 := by
      simpa [pairRepresentation, pairLinear, pairAction, flip] using congrFun he 3
    have h4 : w 2 = w 4 := by
      simpa [pairRepresentation, pairLinear, pairAction, flip] using congrFun he 4
    have h5 : w 0 = w 5 := by
      simpa [pairRepresentation, pairLinear, pairAction, flip] using congrFun he 5
    refine ⟨![w 0,w 1,w 2], Subtype.ext ?_⟩
    change L.coordinates (tripleDouble ![w 0,w 1,w 2]) = v.val
    rw [← hw]
    congr 1
    funext i
    fin_cases i <;> simp [tripleDouble, h3, h4, h5]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Nat.card_fun,
    GaloisField.card 2 2 (by decide)]
  norm_num

theorem A5Placement.reflectionFixedSpace_finrank (P : A5Placement L) :
    Module.finrank Bit P.reflectionFixedSpace = 6 := by
  have hc := P.reflectionFixedSpace_card
  rw [Module.natCard_eq_pow_finrank (K := Bit), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hc

/-- The reflection's six-dimensional fixed space excludes a positive-square
lift once the independent integral fixed-space exclusion is supplied. -/
theorem A5Placement.reflection_lift_of_positive_exclusion (P : A5Placement L)
    (hpositive : ∀ h : LeechIsometryGroup,
      leechCentralProjection h ∈ centralizerI → h ^ 2 = 1 →
      Module.finrank Bit
        ↥(fixedSpace ⊓ LinearMap.ker (difference (leechCentralProjection h))) ≠ 6) :
    ∃ h : LeechIsometryGroup,
      leechCentralProjection h = (P.reflection : LeechCentralQuotient) ∧
        h ^ 2 = negationIsometry := by
  obtain ⟨h, hh⟩ := leechCentralProjection_surjective
    (P.reflection : LeechCentralQuotient)
  have hs : (P.reflection : LeechCentralQuotient) ^ 2 = 1 :=
    congrArg Subtype.val P.reflection_sq
  have hk : h ^ 2 ∈ leechCentralProjection.ker := by
    rw [MonoidHom.mem_ker, map_pow, hh, hs]
  rw [leechCentralProjection_kernel, leechCentralSigns_mem] at hk
  refine ⟨h, hh, ?_⟩
  rcases hk with hk | hk
  · exfalso
    apply hpositive h (hh.symm ▸ (P.le_centralizer P.reflection.property).1) hk
    rw [hh]
    exact P.reflectionFixedSpace_finrank
  · exact hk

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
