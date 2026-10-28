module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.Correction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.ActionSpec
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.ScalarAction
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension

/-!
# From the explicit scalar outer action to a reference tetrahedral actor

The semilinear actor and four-reflection correction are actual lattice maps.
The scalar A₅ centralizes the reference cubic, so an inner scalar adjustment
can make a non-inner scalar automorphism preserve the specified four-point
subgroup without losing centralization. Faithfulness of restriction from
Aut(A₅) to that A₄ rules out an inner action on the tetrahedron.

`ScalarAction` proves the concrete equivariance and non-inner calculation
through the actual icosian scalar sign quotient. Applying that result to the
correction and adjustment gives the unconditional `referenceOuterAction`:
one element centralizing the literal reference cubic, normalizing the marked
scalar A₄, and acting non-innerly on it. No order condition is needed.
Source: Aschbacher, *Sporadic Groups* (1994), 48.3(3), pp.268–269,
and the normalizer step of 49.5, p.284.
-/

open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false


private theorem four_range_fixed (a : alternatingGroup (Fin 5)) :
    a ∈ (alternatingGroup.ofSubtype fourPoints).range ↔ a.val 4 = 4 := by
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro hs
    apply Equiv.Perm.notMem_support.mp
    intro h
    exact (by decide : (4 : Fin 5) ∉ fourPoints) (hs h)
  · intro ha i hi
    fin_cases i <;> simp_all [fourPoints, Equiv.Perm.mem_support]

private theorem adjusted_automorphism (α : MulAut (alternatingGroup (Fin 5))) :
    ∃ g : alternatingGroup (Fin 5), ∀ a : alternatingGroup (Fin 5),
      a ∈ (alternatingGroup.ofSubtype fourPoints).range ↔
        (MulAut.conj g * α) a ∈ (alternatingGroup.ofSubtype fourPoints).range := by
  obtain ⟨σ, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective α
  have hadjust : ∀ i : Fin 5, ∃ g : alternatingGroup (Fin 5),
      g.val i = 4 := by decide +kernel
  obtain ⟨g, hg⟩ := hadjust (σ 4)
  refine ⟨g, ?_⟩
  intro a
  rw [four_range_fixed, four_range_fixed]
  change a.val 4 = 4 ↔ (g.val * (σ * a.val * σ⁻¹) * g.val⁻¹) 4 = 4
  have he : g.val * (σ * a.val * σ⁻¹) * g.val⁻¹ =
      (g.val * σ) * a.val * (g.val * σ)⁻¹ := by group
  rw [he]
  have hi : (g.val * σ)⁻¹ 4 = 4 := ((Equiv.eq_symm_apply (g.val * σ)).mpr hg).symm
  simp only [Equiv.Perm.mul_apply, hi]
  exact ⟨fun h => by rw [h]; exact hg, fun h => (g.val * σ).injective (h.trans hg.symm)⟩

private theorem scalarFive_centralizes (a : alternatingGroup (Fin 5)) :
    scalarFive a ∈ referenceCubicCentralizer := by
  have h : Commute (scalarFive a) RootModel.referenceCubic :=
    icosianScalarProjective_commute (icosianScalarProjectiveAlternating.symm a)
      RootModel.referenceProjective
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  exact (h.zpow_right n).symm.eq

/-- A scalar outer automorphism can be adjusted inside the scalar A₅ to
normalize the literal four-point subgroup. Faithfulness of restriction to
A₄ supplies the non-inner clause, and scalar adjustment preserves the cubic. -/
theorem referenceOuterAction_of_scalar_outer (t : LeechCentralQuotient)
    (ht : t ∈ referenceCubicCentralizer) (α : MulAut (alternatingGroup (Fin 5)))
    (ha : ∀ a, MulAut.conj t (scalarFive a) = scalarFive (α a))
    (ho : ∀ a, α ≠ MulAut.conj a) : ReferenceOuterAction := by
  obtain ⟨g, hg⟩ := adjusted_automorphism α
  let β : MulAut (alternatingGroup (Fin 5)) := MulAut.conj g * α
  have hact (a : alternatingGroup (Fin 5)) :
      MulAut.conj (scalarFive g * t) (scalarFive a) = scalarFive (β a) := by
    rw [map_mul]
    change MulAut.conj (scalarFive g) (MulAut.conj t (scalarFive a)) = _
    rw [ha]
    simp only [β, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  refine ⟨scalarFive g * t, referenceCubicCentralizer.mul_mem
    (scalarFive_centralizes g) ht, ?_, ?_⟩
  · apply Subgroup.mem_normalizer_iff.mpr
    intro i
    constructor
    · rintro ⟨a, rfl⟩
      have hmem := (hg (alternatingGroup.ofSubtype fourPoints a)).mp ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem
      refine ⟨b, ?_⟩
      change scalarFive (alternatingGroup.ofSubtype fourPoints b) =
        MulAut.conj (scalarFive g * t) (scalarFive (alternatingGroup.ofSubtype fourPoints a))
      rw [hact]
      exact congrArg scalarFive hb
    · intro hi
      obtain ⟨a, ha'⟩ := hi
      let b := β.symm (alternatingGroup.ofSubtype fourPoints a)
      have hb : b ∈ (alternatingGroup.ofSubtype fourPoints).range :=
        (hg b).mpr (by change β b ∈ _; simp only [b, MulEquiv.apply_symm_apply]; exact ⟨a, rfl⟩)
      obtain ⟨c, hc⟩ := hb
      refine ⟨c, ?_⟩
      apply (MulAut.conj (scalarFive g * t)).injective
      change MulAut.conj (scalarFive g * t) (scalarFive (alternatingGroup.ofSubtype fourPoints c)) = _
      rw [hact, hc]
      change scalarFive (β (β.symm (alternatingGroup.ofSubtype fourPoints a))) = _
      rw [β.apply_symm_apply]
      exact ha'
  · rintro ⟨j, ⟨a, rfl⟩, hj⟩
    let a' := alternatingGroup.ofSubtype fourPoints a
    have hcard : Nat.card (alternatingGroup.ofSubtype fourPoints).range = 12 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv]
      exact alternatingGroup.card_of_card_eq_four fourPoints_card
    have he : β = MulAut.conj a' :=
      AlternatingFiveSubgroupExtension.restrictionFaithful _ hcard β (MulAut.conj a') (by
        rintro ⟨b, c, rfl⟩
        apply scalarFive_injective
        have h := hj (scalarFour c) ⟨c, rfl⟩
        change MulAut.conj (scalarFive g * t)
          (scalarFive (alternatingGroup.ofSubtype fourPoints c)) =
          MulAut.conj (scalarFive a') (scalarFive (alternatingGroup.ofSubtype fourPoints c)) at h
        rw [hact] at h
        simpa only [MulAut.conj_apply, map_mul, map_inv] using h)
    apply ho (g⁻¹ * a')
    calc
      α = (MulAut.conj g)⁻¹ * β := by dsimp [β]; group
      _ = MulAut.conj (g⁻¹ * a') := by rw [he, map_mul, map_inv]

/-- The four-reflection correction changes no scalar action. The only remaining
premise is the concrete semilinear action on the scalar sign quotient. -/
theorem referenceOuterAction_of_twistScalarOuterAction
    (h : TwistScalarOuterAction) : ReferenceOuterAction := by
  obtain ⟨α, ha, ho⟩ := h
  apply referenceOuterAction_of_scalar_outer Outer.correctedCo1
    Outer.correctedCo1_centralizes α _ ho
  intro a
  let k := icosianProjectiveToCo1 (icosianProjectiveProjection Outer.correctionLift)
  have hk : Outer.correctedCo1 = k⁻¹ * Outer.twistCo1 := by
    change leechCentralProjection ((icosianHermitianToCo0 Outer.correctionLift)⁻¹ *
      Outer.twistCo0) = _
    rw [map_mul, map_inv]
    rfl
  rw [hk, map_mul]
  change MulAut.conj k⁻¹ (MulAut.conj Outer.twistCo1 (scalarFive a)) = _
  rw [ha]
  have hc : Commute (scalarFive (α a)) k :=
    icosianScalarProjective_commute (icosianScalarProjectiveAlternating.symm (α a))
      (icosianProjectiveProjection Outer.correctionLift)
  change k⁻¹ * scalarFive (α a) * (k⁻¹)⁻¹ = _
  rw [hc.inv_right.symm.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- An actual outer actor on the marked scalar tetrahedron in the full
centralizer of the literal reference cubic. The concrete scalar-action proof
discharges the final premise of the corrected lattice construction. -/
theorem referenceOuterAction : ReferenceOuterAction :=
  referenceOuterAction_of_twistScalarOuterAction twistScalarOuterAction

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
