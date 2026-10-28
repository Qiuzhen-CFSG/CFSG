module

public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Candidates
public import Theory.Mathieu.M24.LocalGeometry.SextetCore

/-!
# A common native Sylow marking for the standard octad, sextet and trio

The earlier sextet marking does not stabilize the standard trio. This new
coordinate permutation aligns all three incident objects simultaneously.
The Golay row certificate proves it is a native M24 element. Conjugating
the certified order-1024 subgroup therefore gives an actual Sylow subgroup.
Its two elementary candidates are identified with the intrinsic mapped
sextet core and (assuming its order is 64) trio core.

Source: Aschbacher–Smith H.14 setup and H.14.1(1), printed pp.396–397.
The discovery script is untrusted; every finite identity is kernel checked.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry Subgroup
open PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise

/-- The native coordinate change aligning all three standard objects. -/
def transportPerm : Equiv.Perm (Fin 24) where
  toFun := ![3,7,15,10,23,8,17,13,2,1,18,0,6,19,11,4,9,21,14,16,12,22,20,5]
  invFun := ![11,9,8,0,15,23,12,1,5,16,3,14,20,7,18,2,19,6,10,13,22,17,21,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def rowMessage : Fin 12 → Fin 4096 := ![1144,176,1120,512,1616,1824,96,2672,1076,1602,593,1552]

private theorem transport_rows : ∀ i,
    m24PermuteMask transportPerm (m24GolayRow i) = m24GolayCode (rowMessage i) := by
  decide +kernel

noncomputable def transport : M24 :=
  ⟨transportPerm, by
    exact AffineLiftConstruction.mem_M24_of_rows _
      (fun i => ⟨rowMessage i, transport_rows i⟩)⟩

/-- Both candidates are moved by the same native conjugator. -/
noncomputable def markedCandidate (k : Fin 2) : Subgroup M24 :=
  (EvenCandidates.elementary k).map (MulAut.conj transport).toMonoidHom

noncomputable def standardSylow : Sylow 2 M24 := transport • SextetCore.nativeSylow

theorem standardSylow_coe : standardSylow.toSubgroup =
    SylowNormalizer.candidate.map (MulAut.conj transport).toMonoidHom := rfl

theorem markedCandidate_le_sylow (k : Fin 2) :
    markedCandidate k ≤ standardSylow.toSubgroup :=
  Subgroup.map_mono (EvenCandidates.elementary_le_candidate k)

theorem markedCandidate_elementary (k : Fin 2) :
    IsElementaryAbelian 2 (markedCandidate k) :=
  IsElementaryAbelian.map (MulAut.conj transport).toMonoidHom

theorem markedCandidate_card (k : Fin 2) : Nat.card (markedCandidate k) = 64 := by
  rw [markedCandidate, Subgroup.card_map_of_injective (MulAut.conj transport).injective,
    candidate_card]

theorem standardSylow_le_sextet :
    standardSylow.toSubgroup ≤ sextetStabilizer standardSextet := by
  rw [standardSylow_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    standardSextet.parts = standardSextet.parts
  revert i
  decide +kernel

theorem standardSylow_le_octad :
    standardSylow.toSubgroup ≤ octadStabilizer standardOctad := by
  rw [standardSylow_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    standardOctad.val = standardOctad.val
  revert i
  decide +kernel

theorem standardSylow_le_trio :
    standardSylow.toSubgroup ≤ trioStabilizer standardTrio := by
  rw [standardSylow_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    standardTrio.parts = standardTrio.parts
  revert i
  decide +kernel

private theorem sextetCandidate_fixes_parts : markedCandidate 1 ≤ SextetCore.partFixers := by
  rw [markedCandidate, Subgroup.map_le_iff_le_comap, EvenCandidates.elementary,
    Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro i
  change (standardTetrad i).image
    (fun x => transportPerm ((EvenCandidates.generator 1 a).val (transportPerm.symm x))) = _
  simp only [EvenCandidates.generator_apply]
  revert a i
  decide +kernel

/-- The sextet candidate equals the literal intrinsic sextet core. -/
theorem sextetCandidate_eq_core : markedCandidate 1 = SextetCore.core := by
  have hle := SextetCore.two_subgroup_le_core (markedCandidate 1)
    ((markedCandidate_elementary 1).isPGroup 2 _)
    ((markedCandidate_le_sylow 1).trans standardSylow_le_sextet)
    sextetCandidate_fixes_parts
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [markedCandidate_card, SextetCore.core_ambient_card])

/-- The intrinsic trio core mapped into the native ambient group. -/
noncomputable def trioCore : Subgroup M24 :=
  (pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype

private def translationVector : Fin 6 → Fin 3 → Vector := ![![![0,1,1],![0,0,0],![0,1,1]],![![0,0,0],![0,1,1],![0,1,1]],![![1,0,0],![0,0,0],![1,0,0]],![![1,1,0],![1,1,0],![0,0,0]],![![1,0,1],![0,0,1],![1,0,0]],![![0,1,1],![1,1,0],![1,0,1]]]

private noncomputable def trioGenerator (a : Fin 6) : trioStabilizer standardTrio :=
  ⟨(MulAut.conj transport) (EvenCandidates.generator 0 a),
    standardSylow_le_trio (markedCandidate_le_sylow 0
      ⟨_, EvenCandidates.generator_mem 0 a, rfl⟩)⟩

private theorem trioGenerator_translation (a : Fin 6) :
    HasAffineForm (trioGenerator a) 1 (translationVector a) := by
  intro i v
  change transportPerm ((EvenCandidates.generator 0 a).val (transportPerm.symm (point (i,v)))) = _
  rw [EvenCandidates.generator_apply]
  simp only [Prod.fst_one, Prod.snd_one, Equiv.Perm.one_apply, map_one,
    LinearEquiv.coe_one, id_eq]
  revert a i v
  decide +kernel

/-- The trio candidate lies in the translation kernel and hence in the two-core. -/
theorem trioCandidate_le_core : markedCandidate 0 ≤ trioCore := by
  have hker : (affineQuotient affineCoverage).ker ≤ pCore 2 (trioStabilizer standardTrio) :=
    le_sSup ⟨inferInstance, affineQuotient_kernel_isPGroup affineCoverage⟩
  rw [markedCandidate, Subgroup.map_le_iff_le_comap, EvenCandidates.elementary,
    Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨trioGenerator a, hker (affineQuotient_eq affineCoverage (trioGenerator_translation a)), rfl⟩

/-- Only the independently supplied order of the intrinsic trio core is needed here. -/
theorem trioCandidate_eq_core (hcard : Nat.card trioCore = 64) :
    markedCandidate 0 = trioCore :=
  Subgroup.eq_of_le_of_card_ge trioCandidate_le_core (by rw [hcard, markedCandidate_card])

/-- The native intrinsic sextet and trio cores are distinct. -/
theorem cores_distinct (hcard : Nat.card trioCore = 64) : SextetCore.core ≠ trioCore := by
  rw [← sextetCandidate_eq_core, ← trioCandidate_eq_core hcard]
  intro h
  apply candidates_distinct
  exact (Subgroup.map_injective (MulAut.conj transport).injective) h.symm

/-- Every intrinsic local two-core is contained in this same Sylow subgroup. -/
theorem core_le_sylow (H : Subgroup M24) (hH : standardSylow.toSubgroup ≤ H) :
    (pCore 2 H).map H.subtype ≤ standardSylow.toSubgroup := by
  rintro _ ⟨g, hg, rfl⟩
  exact (pCore_isPGroup.le_sylow_of_normal (standardSylow.subtype hH)) hg

theorem octadCore_le_sylow :
    (pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype ≤
      standardSylow.toSubgroup := core_le_sylow _ standardSylow_le_octad

theorem trioCore_le_sylow : trioCore ≤ standardSylow.toSubgroup :=
  core_le_sylow _ standardSylow_le_trio

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
