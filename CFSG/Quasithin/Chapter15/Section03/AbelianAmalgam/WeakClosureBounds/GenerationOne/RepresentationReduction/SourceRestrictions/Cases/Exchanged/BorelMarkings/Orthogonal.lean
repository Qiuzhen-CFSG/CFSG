module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings.RankOne
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Orthogonal
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison

/-!
# The actual Ω₄⁺ Borel marking

For the determinant action M ↦ A M B⁻¹, the hyperbolic vector e₀ is E₀₀,
and the plane Fe₀ + Fe₁ consists of matrices with zero second row. Thus the
literal line–plane stabilizer corresponds to A upper triangular and B lower
triangular. Conjugating the second SL₂ factor by its Weyl element identifies
the upper/upper Borel with this flag stabilizer. The same model element adjusts
the intertwiner on the literal VectorD 2 F, not a replacement module carrier.

Transporting the product root Sylow proves the Ω₄⁺ Sylow-normalizer marking.
An arbitrary natural-module identification can then be aligned by Sylow
conjugacy, even when the marked pair uses a different concrete field.

Source: Aschbacher–Smith, E.2.2, printed pp.215–216; F.9.18(5)(i), pp.325–326;
and 15.3.65(iii), printed p.1152. The actual determinant/elementary comparison
and its ATLAS attribution are in the imported FourPlusMatrix.Comparison.
-/

@[expose] public noncomputable section
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
open Matrix Matrix.SpecialLinearGroup Representation Representation.BinaryOffender
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
open RemainingModels
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

private theorem elementary_action (g : PairSL (F := F)) (v : VectorD 2 F) :
    omegaNatural (elementaryEquiv g) v =
      coordinates.symm (g.1.val * coordinates v * g.2⁻¹.val) := rfl

private theorem plane_preserved (g : PairSL (F := F)) (hA : g.1.val 1 0 = 0)
    (v : VectorD 2 F) (hv : v ∈ omegaPlane) :
    omegaNatural (elementaryEquiv g) v ∈ omegaPlane := by
  have hv0 : v (.inr 0) = 0 := hv.1
  have hv1 : v (.inr 1) = 0 := hv.2
  rw [elementary_action]
  simp [omegaPlane, coordinates, Matrix.mul_apply, Fin.sum_univ_two, hv0, hv1, hA]

private theorem line_preserved (g : PairSL (F := F))
    (hA : g.1.val 1 0 = 0) (hB : g.2.val 0 1 = 0)
    (v : VectorD 2 F) (hv : v ∈ omegaLine) :
    omegaNatural (elementaryEquiv g) v ∈ omegaLine := by
  have hv1 : v (.inl 1) = 0 := hv.1
  have hv2 : v (.inr 0) = 0 := hv.2.1
  have hv3 : v (.inr 1) = 0 := hv.2.2
  rw [elementary_action]
  simp [omegaLine, coordinates, Matrix.mul_apply, Fin.sum_univ_two,
    adjugate_fin_two, hv1, hv2, hv3, hA, hB]

/-- In determinant coordinates the literal flag stabilizer is the upper/lower pair. -/
theorem elementaryEquiv_mem_omegaBorel_iff (g : PairSL (F := F)) :
    elementaryEquiv g ∈ omegaBorel ↔ g.1.val 1 0 = 0 ∧ g.2.val 0 1 = 0 := by
  constructor
  · intro hg
    have he0 : (e (F := F) 0 : VectorD 2 F) ∈ omegaPlane := by
      simp [omegaPlane, ClassicalOrthogonal.e]
    have h0 := (hg.2 _).mpr he0
    rw [elementary_action] at h0
    have hA11 : g.1.val 1 0 * g.2.val 1 1 = 0 := by
      have := h0.2
      simpa [coordinates, ClassicalOrthogonal.e, Matrix.mul_apply, Fin.sum_univ_two,
        adjugate_fin_two] using this
    have hA01 : g.1.val 1 0 * g.2.val 0 1 = 0 := by
      have := h0.1
      simpa [coordinates, ClassicalOrthogonal.e, Matrix.mul_apply, Fin.sum_univ_two,
        adjugate_fin_two] using this
    have hA : g.1.val 1 0 = 0 := by
      by_contra h
      have h11 := (mul_eq_zero.mp hA11).resolve_left h
      have h01 := (mul_eq_zero.mp hA01).resolve_left h
      have hd := g.2.det_coe
      rw [det_fin_two, h11, h01] at hd
      simp at hd
    refine ⟨hA, ?_⟩
    have ha00 : g.1.val 0 0 ≠ 0 := by
      intro hz
      have hd := g.1.det_coe
      rw [det_fin_two, hz, hA] at hd
      simp at hd
    have hel : (e (F := F) 0 : VectorD 2 F) ∈ omegaLine := by
      simp [omegaLine, ClassicalOrthogonal.e]
    have hl := (hg.1 _).mpr hel
    rw [elementary_action] at hl
    have hB : g.1.val 0 0 * g.2.val 0 1 = 0 := by
      have := hl.1
      simpa [coordinates, ClassicalOrthogonal.e, Matrix.mul_apply, Fin.sum_univ_two,
        adjugate_fin_two] using this
    exact (mul_eq_zero.mp hB).resolve_left ha00
  · rintro ⟨hA, hB⟩
    have hAi : g⁻¹.1.val 1 0 = 0 := by simp [adjugate_fin_two, hA]
    have hBi : g⁻¹.2.val 0 1 = 0 := by simp [adjugate_fin_two, hB]
    constructor
    · intro v
      constructor
      · intro hv
        change v ∈ omegaLine
        have hh := line_preserved g⁻¹ hAi hBi _ hv
        simpa only [map_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply] using hh
      · exact line_preserved g hA hB v
    · intro v
      constructor
      · intro hv
        change v ∈ omegaPlane
        have hh := plane_preserved g⁻¹ hAi _ hv
        simpa only [map_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply] using hh
      · exact plane_preserved g hA v

/-- The second-factor Weyl involution in the literal SL₂ carrier. -/
def secondFactorWeyl : SL(2,F) :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

/-- The genuine two-factor equivalence with the second factor changed by its Weyl element. -/
noncomputable def omegaPairEquiv : PairSL (F := F) ≃* OmegaPlus 2 F :=
  (MulEquiv.prodCongr (MulEquiv.refl _) (MulAut.conj (secondFactorWeyl (F := F)))).trans
    elementaryEquiv

omit [Algebra (ZMod 2) F] in
private theorem weyl_conj_entry (b : SL(2,F)) :
    ((MulAut.conj (secondFactorWeyl (F := F))) b).val 0 1 = b.val 1 0 := by
  change (secondFactorWeyl (F := F) * b * (secondFactorWeyl (F := F))⁻¹).val 0 1 = _
  change ((secondFactorWeyl (F := F)).val * b.val *
    Matrix.adjugate (secondFactorWeyl (F := F)).val) 0 1 = _
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    secondFactorWeyl, adjugate_fin_two, CharTwo.neg_eq]

/-- The adjusted equivalence maps the upper/upper pair to the literal line–plane stabilizer. -/
theorem omegaPairEquiv_borel :
    ((rankOneBorel F).prod (rankOneBorel F)).map omegaPairEquiv.toMonoidHom = omegaBorel := by
  have hiff (g : PairSL (F := F)) : omegaPairEquiv g ∈ omegaBorel ↔
      g ∈ (rankOneBorel F).prod (rankOneBorel F) := by
    change elementaryEquiv (g.1, (MulAut.conj (secondFactorWeyl (F := F))) g.2) ∈ omegaBorel ↔
      (g.1 ∈ rankOneBorel F ∧ g.2 ∈ rankOneBorel F)
    rw [elementaryEquiv_mem_omegaBorel_iff, mem_rankOneBorel_iff, mem_rankOneBorel_iff]
    exact and_congr Iff.rfl (by rw [weyl_conj_entry])
  ext x
  rw [Subgroup.mem_map_equiv, ← hiff, MulEquiv.apply_symm_apply]


/-- The actual Ω₄⁺ flag stabilizer is a Sylow-two normalizer. -/
theorem omega_borel_normalizer [Finite F] :
    ∃ P : Sylow 2 (OmegaPlus 2 F),
      Subgroup.normalizer (P : Set (OmegaPlus 2 F)) = omegaBorel := by
  obtain ⟨P, hP⟩ := Subgroup.exists_sylow_normalizer_prod
    (rankOneBorel F) (rankOneBorel F) (slTwo_borel_normalizer (F := F))
      (slTwo_borel_normalizer (F := F))
  refine ⟨P.mapSurjective (f := (omegaPairEquiv (F := F)).toMonoidHom) (omegaPairEquiv (F := F)).surjective, ?_⟩
  change Subgroup.normalizer ((P : Subgroup (PairSL (F := F))).map
    omegaPairEquiv.toMonoidHom : Set (OmegaPlus 2 F)) = _
  rw [← Subgroup.map_equiv_normalizer_eq]
  change (Subgroup.normalizer (P : Set (PairSL (F := F)))).map _ = _
  rw [hP, omegaPairEquiv_borel]

omit [Algebra (ZMod 2) F] in
/-- The Weyl change is an inner conjugation of the genuine orthogonal actor. -/
theorem omegaPairEquiv_eq_conj (g : PairSL (F := F)) :
    omegaPairEquiv g =
      (MulAut.conj (elementaryEquiv (1, secondFactorWeyl (F := F)))) (elementaryEquiv g) := by
  change elementaryEquiv (g.1, secondFactorWeyl (F := F) * g.2 *
      (secondFactorWeyl (F := F))⁻¹) =
    elementaryEquiv (1, secondFactorWeyl (F := F)) * elementaryEquiv g *
      (elementaryEquiv (1, secondFactorWeyl (F := F)))⁻¹
  simp only [← map_inv, ← map_mul]
  congr 1
  ext <;> simp

/-- The corresponding change of coordinates stays on the literal VectorD 2 F. -/
noncomputable def omegaPairIntertwiner : VectorD 2 F ≃ₗ[ZMod 2] VectorD 2 F :=
  innerIntertwiner omegaNatural (elementaryEquiv (1, secondFactorWeyl (F := F)))

/-- The Weyl-adjusted actor and coordinates intertwine on the literal VectorD carrier. -/
theorem omegaPairIntertwiner_equivariant (g : PairSL (F := F)) (v : VectorD 2 F) :
    omegaPairIntertwiner (onD g v) =
      omegaNatural (omegaPairEquiv g) (omegaPairIntertwiner v) := by
  rw [omegaPairEquiv_eq_conj]
  let z : OmegaPlus 2 F := elementaryEquiv (1, secondFactorWeyl (F := F))
  change omegaNatural z (omegaNatural (elementaryEquiv g) v) =
    omegaNatural (z * elementaryEquiv g * z⁻¹) (omegaNatural z v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
open RemainingModels

/-- A marked pair of SL₂ factors can be aligned with an independently identified
actual Ω₄⁺ natural module, including over a different concrete field carrier. -/
theorem omega_pair_alignment {D V F E : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    (B : Subgroup D) (a : D ≃* PairSL (F := F))
    (hB : B.map a.toMonoidHom = (rankOneBorel F).prod (rankOneBorel F))
    (ρ : Representation (ZMod 2) D V) (φ : D ≃* OmegaPlus 2 E)
    (e : V ≃ₗ[ZMod 2] VectorD 2 E)
    (he : ∀ x v, e (ρ x v) = omegaNatural (φ x) (e v)) :
    ∃ g : OmegaPlus 2 E,
      B.map (φ.trans (MulAut.conj g)).toMonoidHom = omegaBorel ∧
      ∀ x v, (e.trans (innerIntertwiner omegaNatural g)) (ρ x v) =
        omegaNatural ((φ.trans (MulAut.conj g)) x)
          ((e.trans (innerIntertwiner omegaNatural g)) v) := by
  let : Finite D := Finite.of_equiv (PairSL (F := F)) a.symm.toEquiv
  have hpair := Subgroup.exists_sylow_normalizer_prod
    (rankOneBorel F) (rankOneBorel F) (slTwo_borel_normalizer (F := F))
    (slTwo_borel_normalizer (F := F))
  have hsource := Subgroup.exists_sylow_normalizer_of_equiv a _ _ hB hpair
  exact exists_innerIntertwiner_sylowNormalizer _ _ hsource
    (omega_borel_normalizer (F := E)) ρ omegaNatural φ e he

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
