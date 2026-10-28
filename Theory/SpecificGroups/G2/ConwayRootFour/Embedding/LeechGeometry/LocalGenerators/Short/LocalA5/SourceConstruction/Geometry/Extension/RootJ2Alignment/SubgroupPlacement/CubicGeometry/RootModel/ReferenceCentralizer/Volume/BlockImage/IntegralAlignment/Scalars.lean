module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Transport
/-!
# Integral scalar alignment with the literal tetrahedral subgroup

The proved rational scalar marking embeds A₄ into the retained A₅. A nontrivial
involution in its normal four-group has a unique fixed point in the five-point
action, and this point is fixed by the whole A₄. An even permutation moves it to
the literal fifth point. Lifting that permutation through the scalar sign
quotient yields an actual integral Leech isometry.

This supplies the scalar clause of the simultaneous comparison used for
Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5. It asserts no distinguished
cubic or root-four recognition. The imported icosian models retain Gerald Höhn's
ATLAS attribution and the license in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open Long.Block Long.Block.Realization
namespace IntegralAlignment

private def doubleSwap : alternatingGroup fourPoints :=
  ⟨Equiv.swap (⟨0, by decide⟩ : fourPoints) ⟨1, by decide⟩ *
    Equiv.swap (⟨2, by decide⟩ : fourPoints) ⟨3, by decide⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem fixed_point (a : alternatingGroup (Fin 5))
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ p : Fin 5, a.val p = p ∧ ∀ q, a.val q = q → q = p := by
  revert a
  decide +kernel

private theorem marking_fixed (f : alternatingGroup fourPoints →*
    alternatingGroup (Fin 5)) (hf : Function.Injective f) :
    ∃ p : Fin 5, ∀ b, (f b).val p = p := by
  have h2 : doubleSwap ^ 2 = 1 := by decide +kernel
  have hn : doubleSwap ≠ 1 := by decide +kernel
  obtain ⟨p, hp, hu⟩ := fixed_point (f doubleSwap)
    (by rw [← map_pow, h2, map_one]) (by intro h; exact hn (hf (h.trans (map_one f).symm)))
  refine ⟨p, ?_⟩
  intro b
  have hc : Commute (b * doubleSwap * b⁻¹) doubleSwap := by
    change (b * doubleSwap * b⁻¹) * doubleSwap = doubleSwap * (b * doubleSwap * b⁻¹)
    revert b
    decide +kernel
  have he := (hc.map f).eq
  have he' := congrArg (fun g : alternatingGroup (Fin 5) => g.val p) he
  change (f (b * doubleSwap * b⁻¹)).val ((f doubleSwap).val p) =
    (f doubleSwap).val ((f (b * doubleSwap * b⁻¹)).val p) at he'
  rw [hp] at he'
  have hv := hu _ he'.symm
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    Equiv.Perm.mul_apply] at hv
  have hq : (f doubleSwap).val ((f b).val⁻¹ p) = (f b).val⁻¹ p := by
    apply (f b).val.injective
    simpa using hv
  have hbp := hu _ hq
  have := congrArg (f b).val hbp
  simpa using this.symm

private theorem four_range (g : alternatingGroup (Fin 5)) :
    g ∈ (alternatingGroup.ofSubtype fourPoints).range ↔ g.val 4 = 4 := by
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro hs
    apply Equiv.Perm.notMem_support.mp
    intro h
    exact (by decide : (4 : Fin 5) ∉ fourPoints) (hs h)
  · intro hg i hi
    fin_cases i <;> simp_all [fourPoints, Equiv.Perm.mem_support]

private theorem scalar_five_conjugator :
    ∃ g : alternatingGroup (Fin 5),
      rationalScalarToFive.range.map (MulAut.conj g).toMonoidHom =
        (alternatingGroup.ofSubtype fourPoints).range := by
  obtain ⟨p, hp⟩ := marking_fixed rationalTetrahedralMarking
    rationalTetrahedralMarking_injective
  have hex : ∀ p : Fin 5, ∃ g : alternatingGroup (Fin 5), g.val p = 4 := by
    decide +kernel
  obtain ⟨g, hg⟩ := hex p
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro z ⟨b, hb, rfl⟩
    rw [← rationalTetrahedralMarking_range] at hb
    obtain ⟨b, rfl⟩ := hb
    apply (four_range _).mpr
    change g.val ((rationalTetrahedralMarking b).val (g.val⁻¹ 4)) = 4
    have hg' : g.val⁻¹ 4 = p := by rw [← hg]; exact g.val.symm_apply_apply p
    rw [hg', hp, hg]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      rationalScalarToFive_range_card]
    rw [← Nat.card_congr
      (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := fourPoints))).toEquiv]
    exact (alternatingGroup.card_of_card_eq_four fourPoints_card).le

/-- An actual integral scalar sends the rational scalar subgroup to the literal I. -/
theorem exists_scalar_alignment :
    ∃ u : icosianNormOneGroup, ReferenceBlock.scalarImage.map
      (MulAut.conj (leechCentralProjection (icosianScalarsToCo0 u))).toMonoidHom = I := by
  obtain ⟨g, hg⟩ := scalar_five_conjugator
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker
    (icosianScalarProjectiveAlternating.symm g)
  have hproj : leechCentralProjection (icosianScalarsToCo0 u) = scalarFive g := by
    change icosianScalarProjectiveToCo1 (QuotientGroup.mk' icosianNormOneReduction.ker u) = _
    rw [hu]
    rfl
  refine ⟨u, ?_⟩
  rw [hproj, ReferenceBlock.scalarImage, Subgroup.map_map]
  have hc : (MulAut.conj (scalarFive g)).toMonoidHom.comp scalarFive =
      scalarFive.comp (MulAut.conj g).toMonoidHom := by
    ext b
    simp [MulAut.conj_apply]
  rw [hc, ← Subgroup.map_map, hg, MonoidHom.map_range]
  rfl
end IntegralAlignment
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
