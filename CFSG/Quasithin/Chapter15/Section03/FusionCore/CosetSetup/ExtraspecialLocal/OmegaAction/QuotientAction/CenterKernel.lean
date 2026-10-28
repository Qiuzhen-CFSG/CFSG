module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.Conjugation
/-!
# The center-fixing image is the local quotient centralizer

The inclusion-induced equivalence from Y₀/O₂(Y₀) to Z(Y/O₂(Y))
intertwines conjugation by T. Fixing the center is therefore equivalent
to acting trivially on the residual quotient. Its conjugation kernel,
embedded back in T, is exactly the published commutator preimage.
Mapping this equality through the natural orthogonal action gives the
required equality of subgroups of the actual orthogonal actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
calculation after 15.3.49(b), printed p.1143.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

/-- The inclusion-induced equivalence intertwines the two actual conjugation actions. -/
theorem residualCenterEquiv_equivariant (T : Sylow 2 G) (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hn₀ : (T : Subgroup G) ≤ normalizer
      (twoResidualAmbient (Y ⊓ centralizer (V : Set G)) : Set G))
    (t : T) (x : twoResidualAmbient (Y ⊓ centralizer (V : Set G)) ⧸
      pCore 2 (twoResidualAmbient (Y ⊓ centralizer (V : Set G)))) :
    (residualCenterEquiv Y V hc (sylowQuotientConjugation T _ hn₀ t x) : Y ⧸ pCore 2 Y) =
      sylowQuotientConjugation T Y hn t (residualCenterEquiv Y V hc x) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sylowQuotientConjugation_apply, residualCenterEquiv_apply_mk,
    residualCenterEquiv_apply_mk, sylowQuotientConjugation_apply]
  rfl

/-- Fixing the extraspecial center is equivalent to fixing the residual quotient. -/
theorem center_fixing_iff_residual_action (T : Sylow 2 G) (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hn₀ : (T : Subgroup G) ≤ normalizer
      (twoResidualAmbient (Y ⊓ centralizer (V : Set G)) : Set G)) (t : T) :
    sylowQuotientConjugation T Y hn t ∈
      fixingSubgroup (MulAut (Y ⧸ pCore 2 Y)) (center (Y ⧸ pCore 2 Y) : Set (Y ⧸ pCore 2 Y)) ↔
      sylowQuotientConjugation T _ hn₀ t = 1 := by
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro hf
    apply MulEquiv.ext
    intro x
    apply (residualCenterEquiv Y V hc).injective
    apply Subtype.ext
    rw [residualCenterEquiv_equivariant]
    exact hf _ (residualCenterEquiv Y V hc x).property
  · intro hf z hz
    obtain ⟨x, hx⟩ := (residualCenterEquiv Y V hc).surjective ⟨z, hz⟩
    have he := residualCenterEquiv_equivariant T Y V hc hn hn₀ t x
    rw [hf] at he
    change (residualCenterEquiv Y V hc x : Y ⧸ pCore 2 Y) =
      sylowQuotientConjugation T Y hn t (residualCenterEquiv Y V hc x) at he
    change sylowQuotientConjugation T Y hn t z = z
    simpa only [hx] using he.symm

omit [Finite G] in
/-- The published commutator preimage is exactly the embedded quotient-action kernel. -/
theorem commutatorPreimage_eq_quotient_kernel (T : Sylow 2 G) (X : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    commutatorPreimage (T : Subgroup G) X (X.pCoreIn 2) =
      (sylowQuotientConjugation T X hn).ker.map (T : Subgroup G).subtype := by
  have hTK : (T : Subgroup G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    le_sup_right.trans (local_core_normalization (T : Subgroup G) X hn)
  apply le_antisymm
  · intro t ht
    have htT := commutatorPreimage_le (T : Subgroup G) X (X.pCoreIn 2) ht
    refine ⟨⟨t, htT⟩, ?_, rfl⟩
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    apply (quotient_conjugation_fixes_iff T X hn ⟨t, htT⟩ x).mpr
    exact commutator_commutatorPreimage_le _ _ _ hTK
      (commutator_mem_commutator ht x.property)
  · apply le_commutatorPreimage (map_subtype_le _)
    apply commutator_le.mpr
    rintro t ⟨t, ht, rfl⟩ x hx
    apply (quotient_conjugation_fixes_iff T X hn t ⟨x, hx⟩).mp
    exact DFunLike.congr_fun (MonoidHom.mem_ker.mp ht) _

/-- The actual orthogonal image of the local quotient centralizer is the center-fixing image. -/
theorem extraspecialQuotientAction_center_kernel {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hTM : (T : Subgroup G) ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hYM : Y ≤ M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (hn₀ : (T : Subgroup G) ≤ normalizer
      (twoResidualAmbient (Y ⊓ centralizer (V : Set G)) : Set G)) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    d.image (commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2)) =
      centerFixingImage (d.image (T : Subgroup G))
        (extraspecialQuotientAction d T hTM hMY hYM hcore) := by
  dsimp only
  rw [commutatorPreimage_eq_quotient_kernel T _ hn₀]
  let ρ := extraspecialQuotientAction d T hTM hMY hYM hcore
  have hf : ∀ t : T, sylowQuotientConjugation T _ hn₀ t = 1 ↔
      ρ (sylowProjection d T hTM t) ∈
        fixingSubgroup (MulAut (Y ⧸ pCore 2 Y)) (center (Y ⧸ pCore 2 Y) : Set (Y ⧸ pCore 2 Y)) := by
    intro t
    rw [extraspecialQuotientAction_projection]
    exact (center_fixing_iff_residual_action T Y V hc (hTM.trans hMY) hn₀ t).symm
  apply le_antisymm
  · rintro a ⟨m, ⟨t, ht, he⟩, rfl⟩
    have hem : (⟨t, hTM t.property⟩ : M) = m := Subtype.ext he
    refine ⟨sylowProjection d T hTM t, (hf t).mp ht, ?_⟩
    exact congrArg d.actor hem
  · rintro a ⟨p, hp, rfl⟩
    obtain ⟨t, rfl⟩ := sylowProjection_surjective d T hTM p
    refine ⟨⟨t, hTM t.property⟩, ?_, rfl⟩
    exact ⟨t, (hf t).mpr hp, rfl⟩
end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
