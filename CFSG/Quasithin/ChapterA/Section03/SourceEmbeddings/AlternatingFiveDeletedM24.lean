module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedM24Locals
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even.CatalogueCoverage
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.NativeNormalizers
public import Theory.GroupTheory.SylowNormalizerOvergroup
/-!
# The M24 exclusion for a full-Sylow deleted alternating-five block

The original characteristic layer is an elementary subgroup of order sixteen.
Normalization by the full Sylow puts it inside that Sylow. The intrinsic
normal-elementary catalogue and its proved normalizer containments place
both the original block and Sylow in an octad, trio or sextet stabilizer.
Restriction and the native local exclusions contradict the same local
C-component condition. Actual carrier isomorphisms and Sylow conjugation
transport the original block throughout.

Source: Aschbacher–Smith A.3.14 and 10.2.1, using the native local geometry
of GLS3 Table 5.3e. No Sylow-order bound or full normalizer-control premise
is used.
-/
public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
namespace DeletedM24
open ChapterC

private theorem local_transport {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hl : B ∈ localCComponents S)
    (hex : ∀ (T : Sylow 2 H) (A : Subgroup H),
      IsAlternatingBlock A 5 → A ∈ localCComponents T → False) : False := by
  let := Finite.of_equiv G e.toEquiv
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact hex (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap B) hB)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)

private theorem octad_not_local (O : Octad) (S : Sylow 2 (octadStabilizer O))
    (B : Subgroup (octadStabilizer O)) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) : False := by
  obtain ⟨g,hg⟩ := exists_smul_octad_eq O LinearFourCore.seedOctad
  let e : octadStabilizer O ≃* octadStabilizer LinearFourCore.seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  exact local_transport e S B hB hl seed_octad_not_local

private theorem candidate_not_local (k : Fin 2) (S : Sylow 2 (EvenCandidates.localGroup k))
    (B : Subgroup (EvenCandidates.localGroup k)) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) : False := by
  fin_cases k
  · apply local_transport EvenCatalogue.NormalSeeds.trioNormalizerEquiv S B hB hl
    intro _ A hA _
    exact trio_no_deleted A hA
  · exact local_transport EvenCatalogue.NormalSeeds.sextetNormalizerEquiv S B hB hl sextet_not_local

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]
    decide +kernel)

private theorem fixed_not_local (B : Subgroup M24) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24)) : False := by
  let U := (blockU B).map B.subtype
  let := hB.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  have hc : Nat.card U = 16 := (card_map_of_injective B.subtype_injective).trans hB.blockU_card
  have hSU : (markedSylow : Subgroup M24) ≤ normalizer (U : Set M24) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hBU : B ≤ normalizer (U : Set M24) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hUS : U ≤ SylowNormalizer.candidate :=
    (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normalized markedSylow hSU
  let R := U.subgroupOf SylowNormalizer.candidate
  have hRn : R.Normal := normal_subgroupOf_of_le_normalizer hSU
  have hRe : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hUS
  have hR0 : R ≠ ⊥ := by
    intro he
    have hu : U = ⊥ := by
      rw [←map_subgroupOf_eq_of_le hUS]
      change R.map SylowNormalizer.candidate.subtype = ⊥
      rw [he,Subgroup.map_bot]
    rw [hu,card_bot] at hc
    omega
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR0 hRn hRe
  have hUi : U = EvenCatalogue.ambient i := by
    rw [←map_subgroupOf_eq_of_le hUS]
    exact congrArg (Subgroup.map SylowNormalizer.candidate.subtype) hi
  have hBN : B ≤ EvenCatalogue.localGroup i := by
    change B ≤ normalizer (EvenCatalogue.ambient i : Set M24)
    rwa [←hUi]
  have hSN : (markedSylow : Subgroup M24) ≤ EvenCatalogue.localGroup i := by
    change (markedSylow : Subgroup M24) ≤ normalizer (EvenCatalogue.ambient i : Set M24)
    rwa [←hUi]
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · have hBO := hBN.trans hO
    have hSO := hSN.trans hO
    exact octad_not_local O (markedSylow.subtype hSO) (B.subgroupOf (octadStabilizer O))
      (RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBO).symm hB)
      (local_restrict hl hBO)
  · have hBK := hBN.trans hk
    have hSK := hSN.trans hk
    exact candidate_not_local k (markedSylow.subtype hSK) (B.subgroupOf (EvenCandidates.localGroup k))
      (RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBK).symm hB)
      (local_restrict hl hBK)

end DeletedM24
open ChapterC DeletedM24

/-- The specified M24 carrier cannot contain this original normalized local deleted block. -/
theorem alternatingFiveDeleted_not_m24 {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) (S : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (markedSylow : Subgroup M24) := by
    have he := congrArg (fun P : Sylow 2 M24 => (P : Subgroup M24)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    rw [hf,←map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hn).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  exact fixed_not_local (B.map f.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (f.subgroupMap B) hB) hl' hn'
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
