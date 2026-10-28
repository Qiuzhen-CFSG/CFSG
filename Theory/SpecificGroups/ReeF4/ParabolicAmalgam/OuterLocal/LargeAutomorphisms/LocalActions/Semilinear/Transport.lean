module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.RootGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic

/-!
# Transport and diagonal cancellation for Ree local field coordinates

The comparison with a supplied exceptional-root map preserves the actual
matrices. Pulling an automorphism back through this comparison therefore
preserves the two unipotent subgroups and each full signed simple block.
The same comparison transports odd index and generation by the two seeds.

Once a common torus-field formula and an actual fixed-group torus
representative are proved, matrix cancellation gives the requested single
inner correction on all four blocks. These two inputs remain explicit:
this module does not yet recover multiplicativity or realize the torus.
No simplicity, perfectness, or order assumption on the automorphism is used.

Source: GLS3, Table 2.4 and 2.5.1(b,c), and Steinberg, Theorem 36, in
`refs/KGroup/GLS3/chapter2.tex` and `refs/KGroup/GLS3/Chapter2St1.tex`.
The diagonal convention is `T⁻¹ * x * T`; its inner representative is `T⁻¹`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear

open LargeLocalSeeds Theory.AlgebraicGroup
open LocalBlockInput.PairRigidity.BlockParameters
variable {m : ℕ}

/-- Pull an actual model automorphism back to the supplied fixed matrix group. -/
@[expose] def pullback (d : LocalBlockInput m) (c : MulAut (Model m)) :
    MulAut d.fixedGroup :=
  d.modelEquiv.trans (c.trans d.modelEquiv.symm)

theorem modelEquiv_pullback (d : LocalBlockInput m) (c : MulAut (Model m))
    (x : d.fixedGroup) : d.modelEquiv (pullback d c x) = c (d.modelEquiv x) :=
  d.modelEquiv.apply_symm_apply _

private theorem map_pullback (d : LocalBlockInput m) (c : MulAut (Model m))
    (H : Subgroup d.fixedGroup) :
    (H.map (pullback d c).toMonoidHom).map d.modelEquiv.toMonoidHom =
      (H.map d.modelEquiv.toMonoidHom).map c.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext (modelEquiv_pullback d c)

private theorem preserves_pullback (d : LocalBlockInput m) (c : MulAut (Model m))
    (H : Subgroup d.fixedGroup) (K : Subgroup (Model m))
    (hH : H.map d.modelEquiv.toMonoidHom = K)
    (hK : K.map c.toMonoidHom = K) : H.map (pullback d c).toMonoidHom = H := by
  apply Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective
  rw [map_pullback, hH, hK]

/-- Both unipotent preservation hypotheses transfer without extra group assumptions. -/
theorem pullback_preservesUnipotentPair (d : LocalBlockInput m)
    (c : MulAut (Model m)) (hp : PreservesUnipotentPair m c) :
    d.PreservesUnipotentPair (pullback d c) :=
  ⟨preserves_pullback d c _ _ (modelEquiv_map_standardUnipotent d) hp.1,
    preserves_pullback d c _ _ (modelEquiv_map_oppositeUnipotent d) hp.2⟩

/-- Preservation transfers for all four full fixed intersections. -/
theorem pullback_preservesSimpleBlocks (d : LocalBlockInput m)
    (c : MulAut (Model m)) (hc : PreservesSimpleBlocks m c) :
    LocalBlockInput.PairRigidity.PreservesSimpleBlocks d (pullback d c) :=
  fun s positive => preserves_pullback d c _ _
    (modelEquiv_map_simpleBlock d s positive) (hc s positive)

/-- The odd-index hypothesis in the model is also available in supplied coordinates. -/
theorem standardUnipotent_index_odd (d : LocalBlockInput m)
    (hindex : Odd (unipotent m).index) : Odd (standardUnipotent d).index := by
  rwa [unipotent_index_eq_standard d] at hindex

/-- Generation by the two actual fixed seeds transfers in the reverse direction. -/
theorem standardSeed_sup_eq_top (d : LocalBlockInput m)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤) :
    standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ := by
  apply Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective
  rw [Subgroup.map_sup, modelEquiv_map_standardSeed, modelEquiv_map_standardSeed,
    hgen, Subgroup.map_top_of_surjective _ d.modelEquiv.surjective]

theorem modelEquiv_symm_mem_simpleBlock (d : LocalBlockInput m)
    (s : Side) (positive : Bool) {x : Model m} (hx : x ∈ simpleBlock m s positive) :
    d.modelEquiv.symm x ∈ LocalBlockInput.PairRigidity.simpleBlock d s positive := by
  rw [← modelEquiv_map_simpleBlock d s positive] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change d.modelEquiv.symm (d.modelEquiv y) ∈
    LocalBlockInput.PairRigidity.simpleBlock d s positive
  rw [d.modelEquiv.symm_apply_apply]
  exact hy

/-- Matrix comparison commutes with the two automorphism operations in the target. -/
theorem adjusted_pullback_matrix (d : LocalBlockInput m) (c : MulAut (Model m))
    (g x : d.fixedGroup) :
    matrixRepresentation m
        (((MulAut.conj (d.modelEquiv g))⁻¹ * c) (d.modelEquiv x)) =
      (((MulAut.conj g)⁻¹ * pullback d c) x).val.val := by
  have he : d.modelEquiv (((MulAut.conj g)⁻¹ * pullback d c) x) =
      ((MulAut.conj (d.modelEquiv g))⁻¹ * c) (d.modelEquiv x) := by
    change d.modelEquiv (g⁻¹ * pullback d c x * g) =
      (d.modelEquiv g)⁻¹ * c (d.modelEquiv x) * d.modelEquiv g
    rw [map_mul, map_mul, map_inv, modelEquiv_pullback]
  rw [← he, matrixRepresentation_apply]
  exact congrArg Subtype.val (d.modelEquiv_coe _)

/-- A realized diagonal formula in supplied coordinates gives one field action
on all four model blocks. Both substantive inputs are explicitly required. -/
theorem entries_of_fixed_torus (d : LocalBlockInput m) (c : MulAut (Model m))
    (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m)
    (ha : HasTorusFieldAction d (pullback d c) u σ)
    (g : d.fixedGroup) (hg : g.val.val = (torusMatrix u)⁻¹) :
    ∀ s positive, ∀ x ∈ simpleBlock m s positive,
      ∀ i j : F4Chevalley.BasisIndex,
        (matrixRepresentation m (((MulAut.conj (d.modelEquiv g))⁻¹ * c) x) :
          MatrixCarrier m) i j = σ ((matrixRepresentation m x : MatrixCarrier m) i j) := by
  intro s positive x hx i j
  have h := entries_of_torus_realization d (pullback d c) u σ ha g hg
    s positive (d.modelEquiv.symm x) (modelEquiv_symm_mem_simpleBlock d s positive hx) i j
  have he := adjusted_pullback_matrix d c g (d.modelEquiv.symm x)
  rw [d.modelEquiv.apply_symm_apply] at he
  rw [he]
  simpa only [matrixRepresentation_apply, modelEquiv_symm_coe] using h

/-- Conditional assembly of the common inner correction. Field recovery must
produce the compatible parameters, and torus realization must produce a genuine
fixed-group element; neither obligation follows merely from this lemma. -/
theorem common_field_of_recovery_and_realization (d : LocalBlockInput m)
    (c : MulAut (Model m))
    (hparameters : ∃ (u : TorusParameters m)
      (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d (pullback d c) u σ)
    (hrealize : ∀ u : TorusParameters m, TwistCompatible u →
      ∃ g : d.fixedGroup, g.val.val = (torusMatrix u)⁻¹) :
    ∃ (z : Model m) (σ : CoefficientField m ≃+* CoefficientField m),
      ∀ s positive, ∀ x ∈ simpleBlock m s positive,
        ∀ i j : F4Chevalley.BasisIndex,
          (matrixRepresentation m (((MulAut.conj z)⁻¹ * c) x) : MatrixCarrier m) i j =
            σ ((matrixRepresentation m x : MatrixCarrier m) i j) := by
  obtain ⟨u, σ, hu, ha⟩ := hparameters
  obtain ⟨g, hg⟩ := hrealize u hu
  exact ⟨d.modelEquiv g, σ, entries_of_fixed_torus d c u σ ha g hg⟩

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear
