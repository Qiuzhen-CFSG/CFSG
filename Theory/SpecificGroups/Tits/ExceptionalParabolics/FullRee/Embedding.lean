module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction.Center
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction

/-!
# The marked Atlas embedding in the full binary Ree group

Compose the certified Atlas--Parrott equivalence with the fixed root-word
realization. Its image is the derived group and its ten generator images are
specified matrices. This publishes the common map for the remaining local
comparison calculations; it does not assume that any particular parabolic
or Sylow subgroup is its claimed inverse image.

The positive Sylow order shows that the derived subgroup has index two.
Conjugation on it gives a faithful action on the Atlas carrier; its restriction
is exactly the usual inner action. Coverage of every automorphism remains an
independent theorem obligation.

Source: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.12, pp.263--264.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee

/-- The canonical embedding retaining all ten Parrott generator marks. -/
def atlasEmbedding : Atlas1600Group →* ReeF4.Model 0 :=
  InvolutionRootGeometry.embedding.comp parrottFiniteImageEquiv.symm.toMonoidHom

theorem atlasEmbedding_injective : Function.Injective atlasEmbedding :=
  InvolutionRootGeometry.embedding_injective.comp parrottFiniteImageEquiv.symm.injective

theorem atlasEmbedding_generator (i : ParrottGenerator) :
    atlasEmbedding (atlas1600ParrottAssignment i) = InvolutionRootGeometry.fixedGenerator i := by
  have he : parrottFiniteImageEquiv.symm (atlas1600ParrottAssignment i) = parrottGenerator i := by
    apply parrottFiniteImageEquiv.injective
    rw [MulEquiv.apply_symm_apply, parrottFiniteImageEquiv_generator]
  change InvolutionRootGeometry.embedding (parrottFiniteImageEquiv.symm _) = _
  rw [he, InvolutionRootGeometry.embedding_generator]

theorem atlasEmbedding_generator_matrix (i : ParrottGenerator) :
    ReeF4.toSplitGroup 0 (atlasEmbedding (atlas1600ParrottAssignment i)) =
      ReeF4.DerivedTits.Realization.assignment i := by
  rw [atlasEmbedding_generator]
  simpa only [InvolutionRootGeometry.derivedEquiv_coe,
    InvolutionRootGeometry.embedding_generator] using
      InvolutionRootGeometry.derivedEquiv_generator_matrix i

/-- The complete image is the actual derived subgroup of the fixed matrix group. -/
theorem atlasEmbedding_range : atlasEmbedding.range = commutator (ReeF4.Model 0) := by
  rw [← InvolutionRootGeometry.embedding_range]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨parrottFiniteImageEquiv.symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨parrottFiniteImageEquiv x, ?_⟩
    simp only [atlasEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]

/-- Restriction of the fixed embedding, preserving its underlying ambient map. -/
def atlasDerivedEquiv : Atlas1600Group ≃* commutator (ReeF4.Model 0) :=
  parrottFiniteImageEquiv.symm.trans InvolutionRootGeometry.derivedEquiv

@[simp] theorem atlasDerivedEquiv_coe (x : Atlas1600Group) :
    (atlasDerivedEquiv x : ReeF4.Model 0) = atlasEmbedding x := rfl

/-- The full matrix group's actual conjugation action, in Atlas coordinates. -/
def atlasAction : ReeF4.Model 0 →* MulAut Atlas1600Group :=
  (MulAut.congr atlasDerivedEquiv.symm).toMonoidHom.comp
    ReeF4.Parabolics.OuterLocal.binaryDerivedAction

/-- This is conjugation through the fixed embedding, not an unrelated action. -/
theorem atlasAction_apply (g : ReeF4.Model 0) (x : Atlas1600Group) :
    atlasEmbedding (atlasAction g x) = g * atlasEmbedding x * g⁻¹ := by
  change (atlasDerivedEquiv (atlasDerivedEquiv.symm
    (ReeF4.Parabolics.OuterLocal.binaryDerivedAction g (atlasDerivedEquiv x))) : ReeF4.Model 0) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The actual full binary Ree group acts faithfully on the Atlas Tits carrier.
Surjectivity onto all automorphisms is a separate coverage obligation. -/
theorem atlasAction_injective : Function.Injective atlasAction := by
  have h := (ReeF4.Parabolics.OuterLocal.binaryDerivedAction_injective_iff_center_eq_bot
    InvolutionRootGeometry.derivedEquiv.symm).mpr
      ReeF4.Parabolics.OuterLocal.binary_center_eq_bot
  exact (MulAut.congr atlasDerivedEquiv.symm).injective.comp h

/-- The embedded simple subgroup acts by its usual inner automorphisms. -/
theorem atlasAction_embedding (x : Atlas1600Group) :
    atlasAction (atlasEmbedding x) = MulAut.conj x := by
  ext y
  apply atlasEmbedding_injective
  rw [atlasAction_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- The root Sylow order distinguishes the full group from its Tits subgroup. -/
theorem derived_index : (commutator (ReeF4.Model 0)).index = 2 := by
  have hp : commutator (ReeF4.Model 0) ≠ ⊤ :=
    ReeF4.Parabolics.OuterLocal.binaryDerived_ne_top_of_subgroup_card_4096
      InvolutionRootGeometry.derivedEquiv.symm S sylow_card
  have hlow := (commutator (ReeF4.Model 0)).one_lt_index_of_ne_top hp
  have hc : Nat.card (commutator (ReeF4.Model 0)) = 17971200 :=
    (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card
  have hm := (commutator (ReeF4.Model 0)).card_mul_index
  rw [hc] at hm
  have hu := ReeF4.DerivedTits.binary_card_lt
  omega

theorem group_card : Nat.card (ReeF4.Model 0) = 35942400 := by
  have hc : Nat.card (commutator (ReeF4.Model 0)) = 17971200 :=
    (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card
  have hm := (commutator (ReeF4.Model 0)).card_mul_index
  rw [hc, derived_index] at hm
  exact hm.symm

end Tits.ExceptionalParabolics.FullRee
