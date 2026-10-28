module

public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FixedGeneration
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle
public import Theory.Mathieu.M24.ChapterHStabilizers.CommonPlane
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.HexadApplication

/-!
# Native fixed-span inputs for the M22 cocode shadow

The actual sextet translations act faithfully on the sum of tetrad pair spaces:
fixing its pair vectors fixes every letter. Their displacement and the common
four-group's octad fixed space discharge the transvection inputs of H.15.4(4).
The unique elementary subgroup of order 32 in a compatible outer Sylow then
gives four-subgroup fixed-space generation for every rank-five actor.

For inner rank-four actors, the complete native Sylow catalogue reduces to the
hexad kernel and the inner quintet translations. The hexad span is a hyperplane;
the index-two quintet subgroup has full element-fixed span. These are the
rank-five and inner rank-four calculations used in original 8.1.3. The outer
rank-four cases of H.15.5 are not asserted here.

Source: Aschbacher--Smith H.14.3(1), H.15.2, H.15.4--5 and 8.1.3,
printed pp.397--401 and 713--714, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
private theorem pair_span_faithful (g : M24)
    (hg : ∀ u ∈ U7, cocodeRepresentation g u = u) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨B,hB,hi⟩ : ∃ B ∈ m22SourceSextet.parts, i ∈ B := by
    have hi : i ∈ m22SourceSextet.parts.biUnion id := by
      rw [m22SourceSextet.cover]
      exact Finset.mem_univ i
    simpa only [Finset.mem_biUnion, id_eq] using hi
  have hc : B.card = 4 := m22SourceSextet.tetrad B hB
  have hpair (j : Fin 24) (hj : j ∈ B) (hne : i ≠ j) : g.val i ∈ ({i,j} : Finset _) := by
    let P : PointPair := ⟨{i,j}, Finset.card_pair hne⟩
    have hle : supportedPairSpace B ≤ U7 :=
      le_iSup_of_le B (le_iSup_of_le hB le_rfl)
    have hv : pairVector P ∈ U7 := hle
      (pairVector_mem_supportedPairSpace P (by change {i,j} ⊆ B; simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hi,hj⟩))
    have he := (pairVector_fixed_iff g P).mp (hg _ hv)
    change g.val i ∈ P.val
    rw [←he]
    exact Finset.mem_smul_finset.mpr ⟨i,by simp [P],rfl⟩
  obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) i
  obtain ⟨k,hk,hkj⟩ := Finset.exists_mem_ne
    (by rw [Finset.card_erase_of_mem hi,hc]; decide : 1 < (B.erase i).card) j
  have hkB := (Finset.mem_erase.mp hk).2
  have hki := (Finset.mem_erase.mp hk).1
  have hjg := hpair j hj hji.symm
  have hkg := hpair k hkB hki.symm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hjg hkg
  change g.val i = i
  rcases hjg with he | he
  · exact he
  · rcases hkg with he' | he'
    · exact he'
    · exact (hkj (he'.symm.trans he)).elim

/-- Earlier M24 sextet actions and native H.14 quintet data, all discharged. -/
theorem quintet_transvection_inputs : SextetTransvectionInputs where
  kernel_le := by
    change m22OuterQuintetKernel m22SourceSextet ≤ _
    rw [← M22ChapterH.Quintet.outerTranslations_eq_core]
    exact le_rfl
  displacement k hk u hu := by
    obtain ⟨a,ha,rfl⟩ := hk
    rw [←CodeFlags.nativeTranslation_range_eq_core] at ha
    obtain ⟨t,rfl⟩ := ha
    exact SextetLayers.nativeTranslation_displacement m22SourceSextet t hu
  faithful k _ hk := pair_span_faithful k hk
  card_kernel := M22ChapterH.Quintet.core_card

private theorem common_conjugate : E24 =
    M24ChapterHStabilizers.CommonPlane.common.map
      (MulAut.conj m22GeometryConjugator).toMonoidHom := by
  have ho : KO = ((pCore 2 (octadStabilizer standardOctad)).map
      (octadStabilizer standardOctad).subtype).map
        (MulAut.conj m22GeometryConjugator).toMonoidHom := by
    change CFSG.Quasithin.ChapterH.Section13To16.octadKernel m22SourceOctad =
      (CFSG.Quasithin.ChapterH.Section13To16.octadKernel standardOctad).map _
    rw [CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.octadKernel_eq_pointwise,
      CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.octadKernel_eq_pointwise,
      octad_kernel_map _ _ _ m22SourceOctad_eq_smul.symm]
  exact (congrArg₂ (· ⊓ ·) ho M22ChapterH.Sextet.sourceCore_eq_conjugate).trans
    (Subgroup.map_inf _ _ (MulAut.conj m22GeometryConjugator).toMonoidHom
      (MulAut.conj m22GeometryConjugator).injective).symm

private theorem common_elementary : IsElementaryAbelian 2 E24 := by
  rw [common_conjugate]
  let := M24ChapterHStabilizers.CommonPlane.common_elementary
  exact IsElementaryAbelian.map _

private theorem common_card : Nat.card E24 = 4 := by
  exact (Nat.card_congr (MulEquiv.subgroupCongr common_conjugate).toEquiv).trans
    ((card_map_of_injective (K := M24ChapterHStabilizers.CommonPlane.common)
      (f := (MulAut.conj m22GeometryConjugator).toMonoidHom)
      (MulAut.conj m22GeometryConjugator).injective).trans
        M24ChapterHStabilizers.CommonPlane.common_card)

private theorem common_le_pair : E24 ≤ MathieuCode.m22PairStabilizer := by
  intro g hg
  have hgo : g ∈ octadPointwiseKernel m22SourceOctad := by
    have : g ∈ CFSG.Quasithin.ChapterH.Section13To16.octadKernel m22SourceOctad := hg.1
    rwa [CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.octadKernel_eq_pointwise] at this
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  rw [(mem_octadPointwiseKernel _ _).mp hgo i (m22Pair_le_sourceOctad hi)]
  exact hi

private theorem restricted_common_card : Nat.card E = 4 := by
  rw [←card_map_of_injective MathieuCode.m22PairStabilizer.subtype_injective,
    E_map_eq common_le_pair, common_card]

private theorem restricted_common_le : E ≤ K := by
  change E ≤ m22OuterQuintetKernel m22SourceSextet
  rw [←M22ChapterH.Quintet.outerTranslations_eq_core]
  exact fun _ h => h.2

/-- The four-subgroup fixed spaces generate the actual outer M22 cocode.
This is the native H.15.4(4) premise in source 8.1.3. -/
theorem quintet_fourFixedSpan_eq_top :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ := by
  let := M22ChapterH.Quintet.top_isIrreducible
  let := common_elementary
  have hE : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.comap_of_injective MathieuCode.m22PairStabilizer.subtype
      MathieuCode.m22PairStabilizer.subtype_injective E24
  apply fourFixedSpan_eq_top_of_transvections quintet_transvection_inputs
    restricted_common_le hE restricted_common_card common_card
  have hnc : ¬ IsCyclic E24 := by
    intro hc
    let := hc
    obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E24)
    have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E24) g)
    rw [hg,common_card] at hd
    norm_num at hd
  have he : E24 ≤ octadPointwiseKernel m22SourceOctad := by
    rw [←CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.octadKernel_eq_pointwise]
    exact inf_le_left
  have h24 := CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.hexadAmbientFixedInput m22SourceOctad
  rw [h24.noncyclic_fixed E24 he hnc,h24.fixed_finrank]

end CFSG.Quasithin.Chapter8.MathieuShadowRows

namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open MathieuCode.NormalizedShadowRows
/-- Every rank-five elementary subgroup of the full outer M22 actor has
cocode generated by its elementary four-subgroup fixed spaces. -/
theorem rank_five_fourFixedSpan_eq_top (A : Subgroup MathieuCode.m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hr : rank A = 5) :
    fourFixedSpan m22OuterCocodeRepresentation A = ⊤ := by
  have hc : Nat.card A = 32 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have he : rank A = n := by rw [rank,hn,Nat.log_pow Nat.one_lt_two]
    have hn5 : n = 5 := he.symm.trans hr
    rw [hn,hn5]
    rfl
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq MathieuCode.m22PairStabilizer S M22ChapterH.CompatibleSylow.outer
  let f := (MulAut.conj g).toMonoidHom
  have hle : A.map f ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup := by
    have hh := Subgroup.map_mono (f := f) hAS
    change A.map f ≤ (g • S : Sylow 2 MathieuCode.m22PairStabilizer) at hh
    rwa [hg] at hh
  have hK : A.map f = K := (M22ChapterH.CompatibleSylow.outer_card32 _
    (IsElementaryAbelian.map f)
    ((card_map_of_injective (MulAut.conj g).injective).trans hc) hle).trans
      M22ChapterH.Quintet.outerTranslations_eq_core
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (m22OuterCocodeRepresentation.asGroupHom g)
  have hE (b : MathieuCode.m22PairStabilizer) (v : M22Cocode) :
      E (m22OuterCocodeRepresentation b v) = m22OuterCocodeRepresentation (f b) (E v) := by
    change m22OuterCocodeRepresentation g (m22OuterCocodeRepresentation b v) =
      m22OuterCocodeRepresentation (g*b*g⁻¹) (m22OuterCocodeRepresentation g v)
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have ht := fourFixedSpan_map_equivariant m22OuterCocodeRepresentation
    m22OuterCocodeRepresentation f (MulAut.conj g).injective E hE A
  rw [hK,quintet_fourFixedSpan_eq_top] at ht
  apply Submodule.map_injective_of_injective E.injective
  rw [ht,Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective]
end CFSG.Quasithin.Chapter8.MathieuShadowRows

namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open MathieuCode.NormalizedShadowRows
open ChapterH.Section13To16.CocodeLocal
private theorem inner_translations_span :
    fixedSpaceSpan m22CocodeRepresentation M22ChapterH.Sextet.innerTranslations = ⊤ := by
  have he : M22ChapterH.Sextet.innerTranslations.map m22ToPairStabilizer =
      K ⊓ MathieuCode.M22Quintet.L := by
    rw [M22ChapterH.Sextet.innerTranslations_map_pair,
      M22ChapterH.Quintet.outerTranslations_eq_core]
    rfl
  have ht := fixedSpaceSpan_eq_top_of_fourFixedSpan m22OuterCocodeRepresentation
    M22ChapterH.Quintet.innerIntersection_core_index quintet_fourFixedSpan_eq_top
  have hf : Function.Injective m22ToPairStabilizer :=
    fun _ _ he => m22Embedding_injective (congrArg Subtype.val he)
  have hs := fixedSpaceSpan_map_equivariant m22CocodeRepresentation
    m22OuterCocodeRepresentation m22ToPairStabilizer hf
    (LinearEquiv.refl (ZMod 2) M22Cocode) (fun _ _ => rfl)
    M22ChapterH.Sextet.innerTranslations
  rw [he,ht,LinearEquiv.refl_toLinearMap,Submodule.map_id] at hs
  exact hs

/-- The complete inner rank-four calculation: the hexad gives codimension
one, while the inner quintet gives the whole cocode. -/
theorem inner_rank_four_fixedSpan_codim (A : Subgroup M22)
    [IsElementaryAbelian 2 A] (hr : rank A = 4) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22CocodeRepresentation A) ≤ 1 := by
  have hc : Nat.card A = 16 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have he : rank A = n := by rw [rank,hn,Nat.log_pow Nat.one_lt_two]
    have hn4 : n = 4 := he.symm.trans hr
    rw [hn,hn4]
    rfl
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M22 S M22ChapterH.CompatibleSylow.inner
  let f := (MulAut.conj g).toMonoidHom
  have hle : A.map f ≤ M22ChapterH.CompatibleSylow.inner.toSubgroup := by
    have hh := Subgroup.map_mono (f := f) hAS
    change A.map f ≤ (g • S : Sylow 2 M22) at hh
    rwa [hg] at hh
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (m22CocodeRepresentation.asGroupHom g)
  have hE (b : M22) (v : M22Cocode) :
      E (m22CocodeRepresentation b v) = m22CocodeRepresentation (f b) (E v) := by
    change m22CocodeRepresentation g (m22CocodeRepresentation b v) =
      m22CocodeRepresentation (g*b*g⁻¹) (m22CocodeRepresentation g v)
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  rw [fixedSpaceSpan_codim_map_equivariant m22CocodeRepresentation
    m22CocodeRepresentation f (MulAut.conj g).injective E hE]
  rcases M22ChapterH.CompatibleSylow.inner_card16 (A.map f) (IsElementaryAbelian.map f)
      ((card_map_of_injective (MulAut.conj g).injective).trans hc) hle with he | he
  · rw [he,m22_hexad_fixed_dimensions.2]
  · rw [he,inner_translations_span,Submodule.finrank_quotient,finrank_top]
    omega

/-- The inner calculation in the full outer actor, retaining the literal
preimage of native M22 rather than changing automizers. -/
theorem outer_rank_four_fixedSpan_codim_of_inner
    (A : Subgroup MathieuCode.m22PairStabilizer) [IsElementaryAbelian 2 A]
    (hr : rank A = 4) (hi : A ≤ m22ToPairStabilizer.range) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1 := by
  have hf : Function.Injective m22ToPairStabilizer :=
    fun _ _ he => m22Embedding_injective (congrArg Subtype.val he)
  let B := A.comap m22ToPairStabilizer
  have hB : B.map m22ToPairStabilizer = A := map_comap_eq_self hi
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.comap_of_injective _ hf A
  have hrB : rank B = 4 := by
    rw [←rank_map_injective m22ToPairStabilizer hf B,hB,hr]
  have he := fixedSpaceSpan_codim_map_equivariant m22CocodeRepresentation
    m22OuterCocodeRepresentation m22ToPairStabilizer hf
    (LinearEquiv.refl (ZMod 2) M22Cocode) (fun _ _ => rfl) B
  rw [hB] at he
  exact he ▸ inner_rank_four_fixedSpan_codim B hrB
end CFSG.Quasithin.Chapter8.MathieuShadowRows
