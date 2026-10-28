module
public import CFSG.Quasithin.ChapterC.Section03.A5.QuintetCoreObstruction
public import CFSG.Quasithin.ChapterC.Section03.A5.HeptadCoreObstruction
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyTwoReduction
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.M23
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# Mathieu obstructions for a paired alternating block

For an alternating block of degree five whose module has order sixteen in M22
or M23, its module normalizer is of characteristic two, contains the block, and
cannot retain it as a local C-component at a full Sylow subgroup.  The intrinsic
four-space catalogues reduce this to the hexad, quintet, and heptad locals.  The
quintet is excluded by the deleted-module action; the hexad and heptad quotient
actions exclude a local component.  All transports retain the actual block
module, so the resulting normalizer is canonical for the ambient application.

This supplies the M22 and M23 rows in the proof of the paired alternating case
of [AS, 2.4.25], printed page 543.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
private theorem blockU_image (A : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    (blockU (A.map f)).map (A.map f).subtype = ((blockU A).map A.subtype).map f := by
  let e := A.equivMapOfInjective f hf
  rw [← RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

omit [Finite G] [Finite H] in
private theorem blockU_restrict {A P : Subgroup G} (hAP : A ≤ P) :
    ((blockU (A.subgroupOf P)).map (A.subgroupOf P).subtype).map P.subtype =
      (blockU A).map A.subtype := by
  let e := subgroupOfEquivOfLe hAP
  rw [← RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

/-- An actual core image transports the entire block into the marked local. -/
private theorem no_block_of_core_image (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (f : G →* H) (hf : Function.Injective f) (P : Subgroup H)
    (hU : ((blockU A).map A.subtype).map f = (pCore 2 P).map P.subtype)
    (hP : normalizer ((pCore 2 P).map P.subtype : Set H) = P)
    (hex : ∀ B : Subgroup P, IsAlternatingBlock B 5 →
      (blockU B).map B.subtype = pCore 2 P → False) : False := by
  let B := A.map f
  have hB : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (A.equivMapOfInjective f hf) hA
  have hUB : (blockU B).map B.subtype = (pCore 2 P).map P.subtype :=
    (blockU_image A f hf).trans hU
  have hBP : B ≤ P := by
    rw [←hP,←hUB]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hC : IsAlternatingBlock (B.subgroupOf P) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBP).symm hB
  apply hex (B.subgroupOf P) hC
  apply map_injective P.subtype_injective
  exact (blockU_restrict hBP).trans hUB

/-- Conjugate intrinsic cores give an obstruction at the canonical original normalizer. -/
private theorem core_normalizer_obstruction (A P : Subgroup G)
    (hA : IsAlternatingBlock A 5) (e : G ≃* G)
    (hU : (blockU A).map A.subtype = ((pCore 2 P).map P.subtype).map e.toMonoidHom)
    (hP : normalizer ((pCore 2 P).map P.subtype : Set G) = P)
    (hchar : centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hex : ∀ B : Subgroup P, IsAlternatingBlock B 5 →
      (blockU B).map B.subtype = pCore 2 P →
      ∀ S : Sylow 2 P, B ∉ ChapterA.Section03.localCComponents S) :
    let N := normalizer ((blockU A).map A.subtype : Set G)
    N ∈ Chapter1.He G ∧ A ≤ N ∧ ∀ S : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents S := by
  let N := normalizer ((blockU A).map A.subtype : Set G)
  have hN : N = P.map e.toMonoidHom := by
    dsimp only [N]
    rw [hU,←map_equiv_normalizer_eq,hP]
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))
  let r : P ≃* N := (e.subgroupMap P).trans (MulEquiv.subgroupCongr hN.symm)
  let B := (A.subgroupOf N).map r.symm.toMonoidHom
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    ((subgroupOfEquivOfLe hAN).symm.trans (r.symm.subgroupMap (A.subgroupOf N))) hA
  have hr : P.subtype.comp r.symm.toMonoidHom = e.symm.toMonoidHom.comp N.subtype := by
    ext x
    rfl
  have hinv : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  have hBU : (blockU B).map B.subtype = pCore 2 P := by
    apply map_injective P.subtype_injective
    rw [blockU_image _ _ r.symm.injective,map_map,hr,←map_map,blockU_restrict hAN,
      hU,map_map,hinv,map_id]
  refine ⟨Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 r).mp hchar),hAN,?_⟩
  intro S hs
  let : Group.IsSolvable r.symm.toMonoidHom.ker := by
    rw [r.symm.toMonoidHom.ker_eq_bot r.symm.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hs r.symm.toMonoidHom
  exact hex B hB hBU (S.mapSurjective (f := r.symm.toMonoidHom) r.symm.surjective) hl
/-- A two-kernel quotient retains the literal A5 marking of the block image. -/
private noncomputable def alternatingFive_quotient_equiv
    {G H : Type*} [Group G] [Group H]
    (q : G →* H) (hk : IsPGroup 2 q.ker) (A : Subgroup G)
    (hA : IsAlternatingBlock A 5)
    (hcore : (pCore 2 A).map A.subtype ≤ q.ker) :
    A.map q ≃* alternatingGroup (Fin 5) := by
  let f := q.subgroupMap A
  have heker : f.ker = pCore 2 A := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      change IsPGroup 2 (q.subgroupMap A).ker
      rw [Subgroup.ker_subgroupMap]
      exact hk.comap_subtype
    · intro a ha
      apply Subtype.ext
      exact hcore (mem_map_of_mem A.subtype ha)
  let e := (QuotientGroup.quotientMulEquivOfEq heker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective A))
  exact e.symm.trans hA.2.2.quotient_iso.some


private theorem not_local_of_six_core
    {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 6))
    (hchar : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (A : Subgroup X) (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = pCore 2 X) (S : Sylow 2 X) :
    A ∉ ChapterA.Section03.localCComponents S := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
  have hcore : (pCore 2 A).map A.subtype ≤ q.ker := by
    rw [hk]
    rintro _ ⟨a,ha,rfl⟩
    apply hchar
    rw [←hU]
    rintro _ ⟨b,hb,rfl⟩
    exact congrArg A.subtype (hA.2.1.core_centralizes_blockU ha b hb)
  let a := alternatingFive_quotient_equiv q hp A hA hcore
  let := hp.isNilpotent
  intro hl
  exact ChapterA.Section03.SourceEmbeddings.alternatingSix_not_local_five (A.map q) a
    (S.mapSurjective hq) (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)

open Sporadic.Mathieu MathieuCode

private theorem hexad_characteristic :
    centralizer (pCore 2 (m22InnerHexadStabilizer m22SourceOctad) : Set _) ≤
      pCore 2 (m22InnerHexadStabilizer m22SourceOctad) := by
  change centralizer (pCore 2 M22ChapterH.Hexad.Action.Inner : Set _) ≤
    pCore 2 M22ChapterH.Hexad.Action.Inner
  rw [←M22HexadCoordinates.base_stabilizer]
  exact m22Hexad_stabilizer_core_selfCentralizing m22Hexad24Ten_mem

private theorem hexad_not_local
    (A : Subgroup (m22InnerHexadStabilizer m22SourceOctad)) (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = pCore 2 _)
    (S : Sylow 2 (m22InnerHexadStabilizer m22SourceOctad)) :
    A ∉ ChapterA.Section03.localCComponents S := by
  let e := M22ChapterH.Hexad.innerQuotientEquiv.trans
    (Fintype.equivFinOfCardEq MathieuCode.Hexad.CocodeAction.SixPointModel.card_H).altCongrHom
  exact not_local_of_six_core e hexad_characteristic A hA hU S

private theorem hexad_normalizer :
    normalizer (m22InnerHexadKernel m22SourceOctad : Set M22) =
      m22InnerHexadStabilizer m22SourceOctad := by
  rw [←M22HexadCoordinates.base_kernel,m22HexadPointwiseKernel_normalizer m22Hexad24Ten_mem,
    M22HexadCoordinates.base_stabilizer]

private theorem m22_card16_conjugate_intrinsic_core (A : Subgroup M22)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M22,
      A = (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A = (m22InnerQuintetKernel m22SourceSextet).map (MulAut.conj g).toMonoidHom := by
  let := hA
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 M22ChapterH.CompatibleSylow.inner P
  have hP : (P : Subgroup M22) =
      M22ChapterH.CompatibleSylow.inner.toSubgroup.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hc
  have hBS : B ≤ M22ChapterH.CompatibleSylow.inner.toSubgroup := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := (hP ▸ hAP ha)
    have he : (MulAut.conj g⁻¹) a = x := by
      rw [← hxa]
      simp [MulAut.conj_apply, mul_assoc]
    exact he ▸ hx
  have hback : B.map (MulAut.conj g).toMonoidHom = A := by
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id M22 := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, map_id]
  refine ⟨g, ?_⟩
  rcases (M22ChapterH.intrinsic_sylow_catalogue.2.1 B).mp ⟨hB,hBc,hBS⟩ with hb | hb
  · exact Or.inl (hback.symm.trans (congrArg (fun C : Subgroup M22 =>
      C.map (MulAut.conj g).toMonoidHom) hb))
  · exact Or.inr (hback.symm.trans (congrArg (fun C : Subgroup M22 =>
      C.map (MulAut.conj g).toMonoidHom) hb))


/-- The canonical normalizer is an intrinsic obstruction for the original M22 block. -/
theorem m22_normalizer_obstruction (A : Subgroup M22) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) :
    let N := normalizer ((blockU A).map A.subtype : Set M22)
    N ∈ Chapter1.He M22 ∧ A ≤ N ∧ ∀ S : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents S := by
  let := hA.2.1.elementary
  obtain ⟨g,hg⟩ := m22_card16_conjugate_intrinsic_core _ (IsElementaryAbelian.map _) hc
  rcases hg with hh | hq
  · exact core_normalizer_obstruction A _ hA (MulAut.conj g) hh hexad_normalizer
      hexad_characteristic hexad_not_local
  · exfalso
    let f := M22ChapterH.Quintet.quintetInM23.comp (MulAut.conj g⁻¹).toMonoidHom
    have hf : Function.Injective f := M22ChapterH.Quintet.quintetInM23_injective.comp
      (MulAut.conj g⁻¹).injective
    apply no_block_of_core_image A hA f hf M23Geometry.CommonFour.quintetStabilizer ?_
      M23Geometry.quintet_core_normalizer native_quintet_no_alternatingFive_core
    have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id M22 := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    have hu : ((blockU A).map A.subtype).map (MulAut.conj g⁻¹).toMonoidHom =
        m22InnerQuintetKernel m22SourceSextet := by
      rw [hq,map_map,hi,map_id]
    rw [←map_map,hu,M22ChapterH.Quintet.inner_core_image]

/-- The canonical normalizer is an intrinsic obstruction for the original M23 block. -/
theorem m23_normalizer_obstruction (A : Subgroup M23) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) :
    let N := normalizer ((blockU A).map A.subtype : Set M23)
    N ∈ Chapter1.He M23 ∧ A ≤ N ∧ ∀ S : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents S := by
  let := hA.2.1.elementary
  obtain ⟨g,hg⟩ := M23Geometry.CommonFour.card16_conjugate_core _ (IsElementaryAbelian.map _) hc
  rcases hg with hq | hh
  · exfalso
    apply no_block_of_core_image A hA (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
      M23Geometry.CommonFour.quintetStabilizer ?_ M23Geometry.quintet_core_normalizer
      native_quintet_no_alternatingFive_core
    have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id M23 := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [hq,map_map,hi,map_id]
  · apply core_normalizer_obstruction A _ hA (MulAut.conj g) hh
      M23Geometry.source_heptad_core_normalizer ?_ native_heptad_not_local_alternatingFive_core
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      M23Geometry.ChapterHLocalActions.sourceStabilizerEquiv).mp
        M23Geometry.heptadStabilizer_core_selfCentralizing
end CFSG.Quasithin.Chapter2.AlternatingTerminal
