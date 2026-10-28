module

public import Theory.Mathieu.M24.LocalGeometry.Stabilizers.Generation
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# A native M24 geometric pair over every Sylow two-subgroup

The standard sextet's intrinsic two-core is the previously identified E64.
Its ambient centralizer is a two-group by the native permutation calculation,
so its intrinsic centralizer belongs to its two-core. Together with the octad
core theorem and the incident-pair generation theorem, Sylow conjugacy gives
two actual geometric stabilizers containing any supplied Sylow subgroup.

Every automorphism of native M24 is inner and each Sylow two-subgroup is
self-normalizing. Hence an automorphism preserving that Sylow subgroup fixes
all its overgroups. The Frattini argument also makes those overgroups
self-normalizing. These are precisely the invariance and intersection facts
needed when a Sylow subgroup permutes components of a larger finite group.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3e.
The imported native/ATLAS comparison retains its attribution and license in
SextetCore/Comparison.lean and LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.Stabilizers

/-- The intrinsic core of the literal standard sextet stabilizer is self-centralizing. -/
theorem standard_sextet_core_selfCentralizing :
    centralizer (pCore 2 (sextetStabilizer standardSextet) :
      Set (sextetStabilizer standardSextet)) ≤
        pCore 2 (sextetStabilizer standardSextet) := by
  have hc : IsPGroup 2 (centralizer (SextetCore.core : Set M24)) := by
    rw [← SextetCore.candidate_conjugate_core,
      ← Theory.Quasithin.map_centralizer]
    exact (EvenCandidates.centralizer_isPGroup 1).map
      (MulAut.conj SextetCore.transport).toMonoidHom
  let P := sextetStabilizer standardSextet
  have hci : IsPGroup 2 (centralizer (pCore 2 P : Set P)) := by
    have he : centralizer (pCore 2 P : Set P) =
        (centralizer (SextetCore.core : Set M24)).comap P.subtype := by
      ext x
      constructor
      · intro hx y hy
        obtain ⟨q, hq, rfl⟩ := hy
        exact congrArg Subtype.val (hx q hq)
      · intro hx y hy
        apply Subtype.ext
        exact hx y (mem_map_of_mem P.subtype hy)
    rw [he]
    exact hc.comap_of_injective P.subtype P.subtype_injective
  exact le_sSup ⟨inferInstance, hci⟩

/-- Transport an octad by its native permutation action. -/
noncomputable def conjugateOctad (g : M24) (O : Octad) : Octad :=
  ⟨g • O.val, by
    change g • O.val ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← orbit_octad O]
    exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩

/-- Transport the entire sextet partition, retaining all octad conditions. -/
noncomputable def conjugateSextet (g : M24) (X : Sextet) : Sextet where
  parts := g • X.parts
  card := by simpa using X.card
  tetrad := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.mp hA
    simpa using X.tetrad B hB
  disjoint := by
    intro A hA B hB hab
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_smul_finset.mp hB
    change Disjoint (C.image g.val) (D.image g.val)
    exact Finset.disjoint_image g.val.injective |>.mpr
      (X.disjoint C hC D hD (fun he => hab (congrArg (g • ·) he)))
  cover := by
    change (X.parts.image (fun A => A.image g.val)).biUnion id = _
    rw [Finset.image_biUnion]
    change (X.parts.biUnion (fun A => A.image g.val)) = _
    rw [← Finset.biUnion_image]
    change (X.parts.biUnion id).image g.val = _
    rw [X.cover]
    exact Finset.image_univ_of_surjective g.val.surjective
  octad := by
    intro A hA B hB hab
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_smul_finset.mp hB
    have ho := X.octad C hC D hD (fun he => hab (congrArg (g • ·) he))
    have hg := (mem_M24_iff g.val).mp g.property
    change g.val • C ∪ g.val • D ∈ m24Blocks
    rw [← Finset.smul_finset_union]
    change g.val • (C ∪ D) ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← hg]
    exact Set.smul_mem_smul_set ho

/-- The transported octad has the conjugate stabilizer. -/
theorem conjugateOctad_stabilizer (g : M24) (O : Octad) :
    octadStabilizer (conjugateOctad g O) =
      (octadStabilizer O).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g O.val

/-- The transported sextet has the conjugate stabilizer. -/
theorem conjugateSextet_stabilizer (g : M24) (X : Sextet) :
    sextetStabilizer (conjugateSextet g X) =
      (sextetStabilizer X).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g X.parts

/-- A generating pair of actual geometric locals contains any given Sylow two-subgroup. -/
theorem exists_pair_over_sylow (T : Sylow 2 M24) :
    ∃ P Q : Subgroup M24, IsGeometryLocal P ∧ IsGeometryLocal Q ∧
      T.toSubgroup ≤ P ∧ T.toSubgroup ≤ Q ∧
      centralizer (pCore 2 P : Set P) ≤ pCore 2 P ∧
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q ∧
      P ⊔ Q = ⊤ := by
  obtain ⟨g, hg⟩ := SextetCore.exists_conjugate_standardSylow T
  refine ⟨octadStabilizer (conjugateOctad g standardOctad),
    sextetStabilizer (conjugateSextet g standardSextet),
    Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjugateOctad_stabilizer, ← hg]
    exact map_mono SextetCore.standardSylow_le_octadStabilizer
  · rw [conjugateSextet_stabilizer, ← hg]
    exact map_mono SextetCore.standardSylow_le_stabilizer
  · exact LinearFourCore.octad_core_selfCentralizing _
  · rw [conjugateSextet_stabilizer]
    exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) _).mpr
      standard_sextet_core_selfCentralizing
  · rw [conjugateOctad_stabilizer, conjugateSextet_stabilizer, ← Subgroup.map_sup,
      standard_pair_generates, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

/-- A Sylow-preserving automorphism fixes each overgroup of that Sylow subgroup. -/
theorem automorphism_preserves_overgroup (T : Sylow 2 M24)
    (P : Subgroup M24) (hTP : T.toSubgroup ≤ P) (a : MulAut M24)
    (ha : T.toSubgroup.map a.toMonoidHom = T.toSubgroup) :
    P.map a.toMonoidHom = P := by
  obtain ⟨g, rfl⟩ := M24OuterRestriction.conj_surjective a
  have hg : g ∈ normalizer (T.toSubgroup : Set M24) :=
    mem_normalizer_iff_map_conj_eq.mpr ha
  have hgT := SylowNormalizer.sylow_normalizer_le SylowNormalizer.candidate_card
    (SylowNormalizer.candidate_automorphisms_isPGroup SylowNormalizer.candidate_card) T hg
  exact mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (hTP hgT))

/-- Every overgroup of a Sylow two-subgroup is self-normalizing in native M24. -/
theorem sylow_overgroup_selfNormalizing (T : Sylow 2 M24)
    (P : Subgroup M24) (hTP : T.toSubgroup ≤ P) : normalizer (P : Set M24) ≤ P := by
  have hf := le_normalizer_sylow_sup P (normalizer (P : Set M24))
    P.le_normalizer le_rfl (T.subtype hTP)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP] at hf
  exact hf.trans (sup_le
    ((SylowNormalizer.sylow_normalizer_le SylowNormalizer.candidate_card
      (SylowNormalizer.candidate_automorphisms_isPGroup SylowNormalizer.candidate_card) T).trans hTP)
    le_rfl)

end Sporadic.Mathieu.M24LocalGeometry.Stabilizers

end
