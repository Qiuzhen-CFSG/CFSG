module
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Full Sylow images of normalizer-invariant subgroups

A nontrivial subgroup of a Sylow two-subgroup of SL₂ over a finite field
of characteristic two, invariant under its normalizer, is the entire Sylow.
Conjugate to the upper root and use the Borel torus, whose square multipliers
run through all nonzero field elements. Sylow normalizer lifting gives the
same conclusion for the image of any normalizer-invariant subgroup under
a finite-group surjection, even when the kernel is not a two-group.

Source application: the all-abelian Baumann construction in MS93 (5.1),
printed p.913; Glauberman.BaumannRankOneGeneration retains the original
field and kernel in its application.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A nonzero normalizer-invariant part of a binary rank-one Sylow is the full Sylow. -/
theorem subgroup_eq_sylow_of_normalizer_invariant
    (S : Sylow 2 SL(2,F)) (B : Subgroup SL(2,F))
    (hBS : B ≤ (S : Subgroup SL(2,F))) (hB : B ≠ ⊥)
    (hn : normalizer (S : Set SL(2,F)) ≤ normalizer (B : Set SL(2,F))) :
    B = (S : Subgroup SL(2,F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) S
  let e := (MulAut.conj g).toMonoidHom
  have hS : (upperUnipotent F).map e = (S : Subgroup SL(2,F)) :=
    congrArg (fun P : Sylow 2 SL(2,F) => P.toSubgroup) hg
  have hU : B.comap e ≤ upperUnipotent F := by
    have hh := comap_mono (f := e) hBS
    rw [←hS,comap_map_eq_self_of_injective (MulAut.conj g).injective] at hh
    exact hh
  have hne : B.comap e ≠ ⊥ := by
    intro hz
    apply hB
    rw [←map_comap_eq_self_of_surjective (f := e) (MulAut.conj g).surjective B,hz,Subgroup.map_bot]
  have hn' : rankOneBorel F ≤ normalizer (B.comap e : Set SL(2,F)) := by
    apply (map_le_map_iff_of_injective (f := e) (MulAut.conj g).injective).mp
    change (normalizer (upperUnipotent F : Set SL(2,F))).map e ≤ _
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hS,
      map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      map_comap_eq_self_of_surjective (MulAut.conj g).surjective]
    exact hn
  have hh := congrArg (Subgroup.map e) (eq_upperUnipotent_of_normalized _ hU hne hn')
  rwa [map_comap_eq_self_of_surjective (MulAut.conj g).surjective,hS] at hh

variable {G : Type*} [Group G] [Finite G]
/-- Normalizer invariance and escape from the full kernel give the entire Sylow image. -/
theorem normalizer_invariant_image_eq_sylow
    (S : Sylow 2 G) (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (B : Subgroup G) (hBS : B ≤ (S : Subgroup G)) (hB : ¬ B ≤ q.ker)
    (hn : normalizer (S : Set G) ≤ normalizer (B : Set G)) :
    B.map q = (S : Subgroup G).map q := by
  apply subgroup_eq_sylow_of_normalizer_invariant (S.mapSurjective hq) (B.map q)
    (map_mono hBS)
  · exact fun hz => hB ((map_eq_bot_iff B).mp hz)
  · change normalizer ((S : Subgroup G).map q : Set SL(2,F)) ≤ _
    rw [←S.normalizer_map_surjective q hq]
    exact (map_mono hn).trans (B.le_normalizer_map q)
end Matrix.SpecialLinearGroup
