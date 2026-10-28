module
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.Certificates
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage

/-!
# The two elementary normalizers as native geometric stabilizers

The point orbits of the six-generator candidates are respectively three octads
and six tetrads. A normalizing permutation permutes those orbits. The existing
native transporters carry these literal partitions to the standard trio and
sextet, giving one inclusion in the required stabilizer identities.

For the sextet, the transported candidate is the intrinsic two-core, giving
the reverse inclusion by normality. For the trio, its six generator translations
span precisely the triples of binary vectors with sum zero. A 64-word decoding
certificate supplies every such translation. Conjugation by the common affine
linear part preserves their sum, so the whole trio stabilizer normalizes the
candidate. No assertion about placement of arbitrary Sylow pairs is used.

All point labels and decoding tables are checked by Lean's kernel against the
existing native generator coordinates. Source: GLS3, Table 5.3e, and
Aschbacher–Smith 15.3.41–42, printed p.1138; the affine description is
Aschbacher, *Sporadic Groups*, Lemma 20.2.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalSeeds
open Subgroup EvenCandidates
open scoped Pointwise

private def orbitLabel : Fin 2 → Fin 24 → Fin 6 :=
  ![![0,1,1,0,0,2,2,2,0,0,2,0,1,1,2,2,1,2,1,0,1,0,1,2],
    ![0,1,1,2,2,3,4,3,0,0,3,0,5,5,4,4,5,3,5,2,1,2,1,4]]

private def pointOrbit (k : Fin 2) (x : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter (fun y => orbitLabel k y = orbitLabel k x)

private def orbitParts (k : Fin 2) : Finset (Finset (Fin 24)) :=
  Finset.univ.image (pointOrbit k)

private theorem generator_label : ∀ k j x,
    orbitLabel k (generatorPoint k j x) = orbitLabel k x := by decide +kernel

private theorem elementary_label (k : Fin 2) {g : M24} (hg : g ∈ elementary k)
    (x : Fin 24) : orbitLabel k (g.val x) = orbitLabel k x := by
  suffices h : ∀ x, orbitLabel k (g.val x) = orbitLabel k x from h x
  apply closure_induction (k := Set.range (generator k))
    (p := fun g _ => ∀ x, orbitLabel k (g.val x) = orbitLabel k x)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩ x
    rw [generator_apply]
    exact generator_label k j x
  · intro x; rfl
  · intro g h _ _ hg hh x
    change orbitLabel k (g.val (h.val x)) = _
    rw [hg, hh]
  · intro g _ hg x
    have h := hg (g.val.symm x)
    simpa using h.symm

private noncomputable def evaluate (k : Fin 2) : List (Fin 6) → M24
  | [] => 1
  | i :: w => generator k i * evaluate k w

private theorem evaluate_mem (k : Fin 2) (w : List (Fin 6)) : evaluate k w ∈ elementary k := by
  induction w with
  | nil => exact (elementary k).one_mem
  | cons i w ih => exact (elementary k).mul_mem (generator_mem k i) ih

private theorem evaluate_apply (k : Fin 2) (w : List (Fin 6)) (x : Fin 24) :
    (evaluate k w).val x = evaluatePoint k w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (generator k i).val ((evaluate k w).val x) = _
    rw [generator_apply, ih]
    rfl

private theorem witness_transitive : ∀ k x y, orbitLabel k x = orbitLabel k y →
    evaluatePoint k (witnessWord k x y) x = y := by decide +kernel

private theorem orbit_transitive (k : Fin 2) {x y : Fin 24}
    (h : orbitLabel k x = orbitLabel k y) :
    ∃ a ∈ elementary k, a.val x = y :=
  ⟨evaluate k (witnessWord k x y), evaluate_mem _ _,
    (evaluate_apply _ _ _).trans (witness_transitive k x y h)⟩

private theorem pointOrbit_card : ∀ k x, (pointOrbit k x).card = if k = 0 then 8 else 4 := by
  decide +kernel

private theorem normalizer_smul_pointOrbit (k : Fin 2) {g : M24}
    (hg : g ∈ EvenCandidates.localGroup k) (x : Fin 24) :
    g • pointOrbit k x = pointOrbit k (g.val x) := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, hax⟩ := orbit_transitive k ((Finset.mem_filter.mp hy).2.symm)
    have hc : g * a * g⁻¹ ∈ elementary k := (mem_set_normalizer_iff.mp hg a).mp ha
    have he := elementary_label k hc (g.val x)
    have hp : (g * a * g⁻¹).val (g.val x) = g.val y := by
      change g.val (a.val (g.val.symm (g.val x))) = _
      rw [g.val.symm_apply_apply, hax]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change orbitLabel k (g.val y) = orbitLabel k (g.val x)
    rwa [hp] at he
  · rw [Finset.card_smul_finset, pointOrbit_card, pointOrbit_card]

private theorem normalizer_le_orbit_stabilizer (k : Fin 2) :
    EvenCandidates.localGroup k ≤ MulAction.stabilizer M24 (orbitParts k) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
  rw [normalizer_smul_pointOrbit k hg]
  exact Finset.mem_image.mpr ⟨g.val x, Finset.mem_univ _, rfl⟩

private theorem trio_orbitParts : orbitParts 0 = FourNormalizers.rowGeometry 2 := by decide +kernel

private theorem sextet_orbitParts : SextetCore.transport • orbitParts 1 = standardSextet.parts := by
  decide +kernel

private theorem trio_normalizer_le : EvenCandidates.localGroup 0 ≤
    MulAction.stabilizer M24 (FourNormalizers.rowGeometry 2) := by
  rw [← trio_orbitParts]
  exact normalizer_le_orbit_stabilizer 0

private theorem sextet_normalizer_map_le :
    (EvenCandidates.localGroup 1).map (MulAut.conj SextetCore.transport).toMonoidHom ≤
      sextetStabilizer standardSextet := by
  have h := Subgroup.map_mono (f := (MulAut.conj SextetCore.transport).toMonoidHom)
    (normalizer_le_orbit_stabilizer 1)
  rwa [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, sextet_orbitParts] at h

/-- Conjugating the literal second candidate normalizer gives exactly the
standard sextet stabilizer. -/
theorem sextet_normalizer_map_eq :
    (EvenCandidates.localGroup 1).map (MulAut.conj SextetCore.transport).toMonoidHom =
      sextetStabilizer standardSextet := by
  apply le_antisymm sextet_normalizer_map_le
  rw [EvenCandidates.localGroup, map_equiv_normalizer_eq,
    SextetCore.candidate_conjugate_core]
  apply (normal_subgroupOf_iff_le_normalizer SextetCore.core_le_stabilizer).mp
  have he : SextetCore.core.subgroupOf (sextetStabilizer standardSextet) =
      pCore 2 (sextetStabilizer standardSextet) := by
    ext g
    exact mem_map_iff_mem (sextetStabilizer standardSextet).subtype_injective
  rw [he]
  infer_instance

open PairOvergroups PairOvergroups.QuotientConstruction

private noncomputable def trioCandidate : Subgroup M24 :=
  (elementary 0).map (MulAut.conj (FourNormalizers.certificateElement 0)).toMonoidHom

private def word (m : Fin 64) : List (Fin 6) :=
  (List.finRange 6).filter (fun j => m.val.testBit j.val)

private def wordVector (m : Fin 64) : Fin 3 → Vector :=
  (word m).foldr (fun j t => FourNormalizers.translationVector j + t) 0

private def decode : Fin 8 → Fin 8 → Fin 64 :=
  ![![0,8,31,23,20,28,11,3], ![33,41,62,54,53,61,42,34],
    ![27,19,4,12,15,7,16,24], ![58,50,37,45,46,38,49,57],
    ![56,48,39,47,44,36,51,59], ![25,17,6,14,13,5,18,26],
    ![35,43,60,52,55,63,40,32], ![2,10,29,21,22,30,9,1]]

private theorem wordVector_decode : ∀ t : Fin 3 → Vector, (∑ i, t i) = 0 →
    wordVector (decode (vectorIndex (t 0)) (vectorIndex (t 1))) = t := by decide +kernel

private theorem wordPoint : ∀ m i v,
    FourNormalizers.certificatePerm 0
      (evaluatePoint 0 (word m) ((FourNormalizers.certificatePerm 0).symm (point (i,v)))) =
        point (i, v + wordVector m i) := by decide +kernel

private theorem balanced_translation_mem (t : Fin 3 → Vector) (ht : (∑ i, t i) = 0) :
    ∃ u ∈ trioCandidate, ∀ i v, u.val (point (i,v)) = point (i,v + t i) := by
  let m := decode (vectorIndex (t 0)) (vectorIndex (t 1))
  let c := FourNormalizers.certificateElement 0
  refine ⟨c * evaluate 0 (word m) * c⁻¹, ⟨evaluate 0 (word m), evaluate_mem _ _, rfl⟩, ?_⟩
  intro i v
  change FourNormalizers.certificatePerm 0
    ((evaluate 0 (word m)).val ((FourNormalizers.certificatePerm 0).symm (point (i,v)))) = _
  rw [evaluate_apply, wordPoint, wordVector_decode t ht]

private theorem translationVector_sum : ∀ j, (∑ i, FourNormalizers.translationVector j i) = 0 := by
  decide +kernel

private theorem conjugate_generator_mem (g : trioStabilizer standardTrio) (j : Fin 6) :
    g.val * (FourNormalizers.certificateElement 0 * generator 0 j *
      (FourNormalizers.certificateElement 0)⁻¹) * g.val⁻¹ ∈ trioCandidate := by
  obtain ⟨q, t, hg⟩ := affineCoverage g
  let L := Matrix.SpecialLinearGroup.toLin' q.2
  let s : Fin 3 → Vector := fun i => L (FourNormalizers.translationVector j (q.1.symm i))
  have hs : (∑ i, s i) = 0 := by
    change (∑ i, L (FourNormalizers.translationVector j (q.1.symm i))) = 0
    rw [← map_sum, Equiv.sum_comp, translationVector_sum, map_zero]
  obtain ⟨u, hu, hpoint⟩ := balanced_translation_mem s hs
  have he : g.val * (FourNormalizers.certificateElement 0 * generator 0 j *
      (FourNormalizers.certificateElement 0)⁻¹) * g.val⁻¹ = u := by
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨i,v⟩, rfl⟩ := point.surjective x
    change g.val.val ((FourNormalizers.certificateElement 0 * generator 0 j *
      (FourNormalizers.certificateElement 0)⁻¹).val (point (i,v))) =
        u.val (g.val.val (point (i,v)))
    rw [FourNormalizers.generator_translation, hg, hg, hpoint]
    simp only [s, L, q.1.symm_apply_apply, map_add, add_right_comm]
  exact he ▸ hu

private theorem trio_stabilizer_le_normalizer :
    trioStabilizer standardTrio ≤ normalizer (trioCandidate : Set M24) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · apply (map_le_iff_le_comap).mpr
    change (elementary 0).map (MulAut.conj (FourNormalizers.certificateElement 0)).toMonoidHom ≤ _
    apply (map_le_iff_le_comap).mpr
    apply (closure_le (K := _)).mpr
    rintro _ ⟨j, rfl⟩
    exact conjugate_generator_mem ⟨g, hg⟩ j
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- Conjugating the literal first candidate normalizer gives exactly the
standard trio stabilizer. -/
theorem trio_normalizer_map_eq :
    (EvenCandidates.localGroup 0).map
      (MulAut.conj (FourNormalizers.certificateElement 0)).toMonoidHom =
        trioStabilizer standardTrio := by
  apply le_antisymm
  · have h := Subgroup.map_mono
      (f := (MulAut.conj (FourNormalizers.certificateElement 0)).toMonoidHom) trio_normalizer_le
    rwa [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      FourNormalizers.transport_geometry] at h
  · rw [EvenCandidates.localGroup, map_equiv_normalizer_eq]
    exact trio_stabilizer_le_normalizer

/-- The native conjugation isomorphism for the first elementary normalizer. -/
noncomputable def trioNormalizerEquiv :
    EvenCandidates.localGroup 0 ≃* trioStabilizer standardTrio :=
  ((MulAut.conj (FourNormalizers.certificateElement 0)).subgroupMap _).trans
    (MulEquiv.subgroupCongr trio_normalizer_map_eq)

/-- The native conjugation isomorphism for the second elementary normalizer. -/
noncomputable def sextetNormalizerEquiv :
    EvenCandidates.localGroup 1 ≃* sextetStabilizer standardSextet :=
  ((MulAut.conj SextetCore.transport).subgroupMap _).trans
    (MulEquiv.subgroupCongr sextet_normalizer_map_eq)

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalSeeds
