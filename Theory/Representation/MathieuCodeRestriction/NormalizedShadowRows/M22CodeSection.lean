module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpace
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Transvections
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle
/-!
# The literal quintet code axis

The earlier sextet displacement and faithful pair-space action construct the
full cocode action data. Duality identifies the actual five-dimensional axis
V9/V4 with the quintet kernel K under conjugation. Full transvections on the
six-dimensional quotient show that a code vector lies in V9 precisely when
all K-displacements lie in V4. The original Chapter 8 pair uses this criterion
to identify B, before transporting its literal quotient B/U.

The elementary pair-vector faithfulness argument is the native extraction of
Chapter8.MathieuShadowRows.quintet_transvection_inputs. All other earlier
inputs are supplied by the existing native H.14 and H.15 proofs.
Source: Aschbacher--Smith H.14.3(2), H.15.4(1--2), H.16.3(3), and 8.2.8,
printed pp.397,400,403,718--719, refs/quasithin.pdf. The underlying Golay and
hexacode constructions are the licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped Pointwise IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
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
theorem transvection_inputs : SextetTransvectionInputs where
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


local instance : IsIrreducible (innerConjugation M22ChapterH.Quintet.innerInputs) :=
  M22ChapterH.Quintet.innerConjugation_isIrreducible

@[expose] def flag : DualAction.CocodeFlag := chiefFlagOfEarlierData transvection_inputs
  M22ChapterH.Quintet.innerInputs M22ChapterH.Quintet.partAction_ker M22ChapterH.Quintet.quotientEquiv

@[expose] def actionData : DualAction.CocodeActionData flag (Additive M22Quintet.K) :=
  actionDataOfEarlierData transvection_inputs M22ChapterH.Quintet.innerInputs
    M22ChapterH.Quintet.partAction_ker M22ChapterH.Quintet.quotientEquiv

@[expose] def axisMarking : DualAction.codeAxis ≃ₗ[ZMod 2] Additive M22Quintet.K :=
  actionData.codeAxisEquiv

theorem axisMarking_equivariant (g : Q) (v : DualAction.codeAxis) :
    axisMarking (flag.codeAxisAction g v) = kernelConjugation g (axisMarking v) :=
  actionData.codeAxisEquiv_equivariant g v

theorem nine_dim : Module.finrank (ZMod 2) V9 = 9 := flag.code_dimensions.2.2

theorem nine_invariant (g : Q) (v : M22Code) (hv : v ∈ V9) :
    m22OuterCodeRepresentation g.val v ∈ V9 := by
  have h := flag.codeNine.apply_mem_toSubmodule g
  rw [flag.codeNine_space] at h
  exact h hv

/-- The axis marking on original code representatives avoids unfolding the
constructed chief flag at downstream action boundaries. -/
theorem axisMarking_mk_equivariant (g : Q) (v : M22Code) (hv : v ∈ V9) :
    axisMarking ⟨V4.mkQ (m22OuterCodeRepresentation g.val v),
      ⟨m22OuterCodeRepresentation g.val v,nine_invariant g v hv,rfl⟩⟩ =
      kernelConjugation g (axisMarking ⟨V4.mkQ v,⟨v,hv,rfl⟩⟩) :=
  axisMarking_equivariant g ⟨V4.mkQ v,⟨v,hv,rfl⟩⟩

theorem four_le_nine : V4 ≤ V9 :=
  (show V4 ≤ V8 from flag.code_strict.2.1.le).trans V8_le_V9

theorem displacement_iff (v : M22Code) :
    (∀ k : M22Quintet.K, m22OuterCodeRepresentation k.val v - v ∈ V4) ↔ v ∈ V9 := by
  have hmem : V4.mkQ v ∈ DualAction.codeAxis ↔ v ∈ V9 := by
    change v ∈ (V9.map V4.mkQ).comap V4.mkQ ↔ _
    rw [Submodule.comap_map_mkQ,sup_eq_right.mpr four_le_nine]
  constructor
  · intro hv
    apply hmem.mp
    obtain ⟨f,hf,haxis,hfull⟩ := actionData.codeQuotient_transvections
    by_contra hout
    have hfv : f (V4.mkQ v) ≠ 0 := by
      intro he
      exact hout (haxis ▸ (show V4.mkQ v ∈ f.ker from he))
    have hfv1 : f (V4.mkQ v) = 1 :=
      (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hfv
    have hne : DualAction.codeAxis ≠ ⊥ := by
      intro he
      have hd := actionData.codeAxis_dim
      rw [he,finrank_bot] at hd
      omega
    obtain ⟨w,hw,hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hfw : f w = 0 := show w ∈ f.ker from haxis.symm ▸ hw
    obtain ⟨k,hk⟩ := (hfull (BinaryLinear.transvection w f hfw)).mpr ⟨w,hfw,rfl⟩
    have hfix : DualAction.codeQuotientKernelAction k (V4.mkQ v) = V4.mkQ v :=
      (Submodule.Quotient.eq V4).mpr (hv k)
    rw [hk] at hfix
    change V4.mkQ v + f (V4.mkQ v) • w = V4.mkQ v at hfix
    rw [hfv1,one_smul] at hfix
    exact hwne (add_left_cancel (hfix.trans (add_zero _).symm))
  · intro hv k
    apply (Submodule.Quotient.eq V4).mp
    have hk : DualAction.codeQuotientKernelAction k ∈ BinaryLinear.radical DualAction.codeAxis :=
      actionData.codeQuotientKernelAction_full ▸ (show DualAction.codeQuotientKernelAction k ∈
        DualAction.codeQuotientKernelAction.range from ⟨k,rfl⟩)
    exact hk.1 _ (hmem.mpr hv)

end MathieuCode.NormalizedShadowRows.M22CodeSection
