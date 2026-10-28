module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Comparison
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Normalizer.InvariantForm
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# The full linear normalizer of the six-dimensional binary A₈ action

Conjugation by a normalizer pulls the split quadratic form back to an
A₈-invariant nonzero quadratic form. Uniqueness of that form forces the
normalizer to be an isometry. The checked faithful S₈ action and the geometric
upper bound of 40320 on the isometry group then identify every such isometry
with a coordinate permutation. Conversely, normality of A₈ in S₈ gives the
reverse inclusion, literally in the units of the endomorphism ring of the
natural deleted module.

This proves the linear-normalizer step in Aschbacher–Smith K.3.2.2
(printed p.455/PDF p.466) and B.4.2(10) (printed p.86/PDF p.97).
The quadratic comparison and isometry-group bound come from the attributed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

noncomputable section

namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
open Atlas.Order20160A8 ClassicalOrthogonal DeletedEight BinaryPermutation
open Representation.BinaryOffender

private def splitToNatural : VectorD 3 (ZMod 2) ≃ₗ[ZMod 2] natural (Fin 8) :=
  splitEquiv.trans deletedEightEquivNatural

private theorem splitToNatural_intertwines (p : Equiv.Perm (Fin 8)) (x : VectorD 3 (ZMod 2)) :
    splitToNatural ((orthogonalHom p).val x) =
      naturalRepresentation (Fin 8) p (splitToNatural x) := by
  change deletedEightEquivNatural
    (splitEquiv (splitEquiv.symm (quotientPerm p (splitEquiv x)))) = _
  rw [LinearEquiv.apply_symm_apply, deletedEightEquivNatural_intertwines]
  rfl

private theorem orthogonalHom_surjective : Function.Surjective orthogonalHom := by
  apply ((Nat.bijective_iff_injective_and_card orthogonalHom).mpr
    ⟨orthogonalHom_injective, ?_⟩).surjective
  apply le_antisymm (Nat.card_le_card_of_injective _ orthogonalHom_injective)
  have hc : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hc]
  exact Geometry.orthogonal_card_le

/-- The full linear normalizer of the binary natural A₈ action is precisely
its natural S₈ extension. This supplies the ambient-group step in K.3.2.2. -/
public theorem linearNormalizer_alternatingNatural_eq :
    linearNormalizer (alternatingNaturalRepresentation (Fin 8)) =
      actionImage (naturalRepresentation (Fin 8)) := by
  apply le_antisymm
  · intro n hn
    let g := (splitToNatural.trans
      (LinearMap.GeneralLinearGroup.toLinearEquiv n)).trans splitToNatural.symm
    have hconj (p : alternatingGroup (Fin 8)) : ∃ r : alternatingGroup (Fin 8),
        ∀ x, g ((orthogonalHom p.val).val x) = (orthogonalHom r.val).val (g x) := by
      have hm : n * (alternatingNaturalRepresentation (Fin 8)).asGroupHom p * n⁻¹ ∈
          actionImage (alternatingNaturalRepresentation (Fin 8)) :=
        (Subgroup.mem_normalizer_iff.mp hn _).mp ⟨p, rfl⟩
      obtain ⟨r, hr⟩ := hm
      have hc : (alternatingNaturalRepresentation (Fin 8)).asGroupHom r * n =
          n * (alternatingNaturalRepresentation (Fin 8)).asGroupHom p := by
        rw [hr]
        group
      have hv (v : natural (Fin 8)) :
          n.val (alternatingNaturalRepresentation (Fin 8) p v) =
            alternatingNaturalRepresentation (Fin 8) r (n.val v) :=
        (congrArg (fun u : (Module.End (ZMod 2) (natural (Fin 8)))ˣ => u.val v) hc).symm
      refine ⟨r, fun x => ?_⟩
      apply splitToNatural.injective
      change splitToNatural (splitToNatural.symm
        (n.val (splitToNatural ((orthogonalHom p.val).val x)))) =
          splitToNatural ((orthogonalHom r.val).val
            (splitToNatural.symm (n.val (splitToNatural x))))
      rw [LinearEquiv.apply_symm_apply, splitToNatural_intertwines,
        splitToNatural_intertwines, LinearEquiv.apply_symm_apply]
      exact hv (splitToNatural x)
    let h : O_DPlus 3 (ZMod 2) := ⟨g,
      (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
        (Normalizer.preserves_form g hconj)⟩
    obtain ⟨p, hp⟩ := orthogonalHom_surjective h
    refine ⟨p, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := splitToNatural.surjective v
    have he := congrArg (fun k : O_DPlus 3 (ZMod 2) => splitToNatural (k.val x)) hp
    rw [splitToNatural_intertwines] at he
    change naturalRepresentation (Fin 8) p (splitToNatural x) =
      splitToNatural (splitToNatural.symm (n.val (splitToNatural x))) at he
    simpa only [Representation.asGroupHom_apply, LinearEquiv.apply_symm_apply] using he
  · exact actionImage_le_linearNormalizer (naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8))

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
