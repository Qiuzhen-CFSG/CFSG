module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelBaer
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# The original fixed subgroup's span under the moved-plane centralizer

Baer–Suzuki places E in Q=O₂(C_G(U)). The C_G(U)-span of E therefore
remains in Q. Normal-span commutator transport confines [Q,F] to U,
and preservation of E and C_G(U) by T makes F invariant under T.
Each original centralizer conjugate of E is also normalized by Q.
Source ordering then makes the span invariant under the actual partner Mc.
These are containment and normalization facts for the span and its
individual conjugates; they do not identify every conjugate with E.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizer span lies in its two-core, has displacement
inside U, and is normalized by both the centralizer and the chosen Sylow. -/
theorem PreparedChosenModule.extraspecial_kernel_span_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let E := thompsonFixed T V
    let C := centralizer (U : Set G)
    let Q := C.pCoreIn 2
    let F := conjugateSpanBy E C
    F ≤ Q ∧ ⁅Q,F⁆ ≤ U ∧ C ≤ normalizer (F : Set G) ∧
      (T : Subgroup G) ≤ normalizer (F : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  have hEQ : E ≤ Q := h.extraspecial_moved_fixed_le_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hEC : E ≤ C := hEQ.trans (pCoreIn_le 2 C)
  have hCQ : C ≤ normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hFQ : F ≤ Q := conjugateSpanBy_le hEQ hCQ
  have hdisp : ⁅Q,E⁆ ≤ U := h.extraspecial_moved_centralizer_core_displacement
    hG T hempty hM hmany hJ hu hfull hex
  have hQF : ⁅Q,F⁆ ≤ U := by
    change ⁅Q,conjugateSpanBy E C⁆ ≤ U
    rw [commutator_comm,commutator_conjugateSpanBy_of_normalized_right E C Q hEC hCQ]
    exact conjugateSpanBy_le ((commutator_comm E Q).trans_le hdisp)
      (Subgroup.centralizer_le_normalizer _)
  have hTJ : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) :=
    ChapterB.le_normalizer_thompsonJ (T : Subgroup G) 1
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    have htV : V.map (MulAut.conj t).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hM.1.2 ht))
    have htJ : (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom =
        ChapterB.thompsonJ (T : Subgroup G) 1 :=
      mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    change (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆).map (MulAut.conj t).toMonoidHom = _
    rw [map_commutator,htV,htJ]
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    hTU.trans (normalizer_le_normalizer_centralizer _)
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  exact ⟨hFQ,hQF,le_normalizer_conjugateSpanBy E C,
    normalizes_conjugateSpanBy E C (T : Subgroup G) hTE hTC⟩

/-- Every original centralizer conjugate lies in Q and T and is normalized
by Q. No equality of the conjugate with E is asserted. -/
theorem PreparedChosenModule.extraspecial_kernel_conjugate_fixed_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let E := thompsonFixed T V
    let C := centralizer (U : Set G)
    let Q := C.pCoreIn 2
    ∀ g ∈ C, E.map (MulAut.conj g).toMonoidHom ≤ Q ∧
      E.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      Q ≤ normalizer (E.map (MulAut.conj g).toMonoidHom : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  have hEQ : E ≤ Q := h.extraspecial_moved_fixed_le_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQT : Q ≤ (T : Subgroup G) := hcore.2.1
  have hQE : Q ≤ normalizer (E : Set G) := hcore.2.2.1
  have hCQ : C ≤ normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  change ∀ g ∈ C, E.map (MulAut.conj g).toMonoidHom ≤ Q ∧
    E.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
    Q ≤ normalizer (E.map (MulAut.conj g).toMonoidHom : Set G)
  intro g hg
  have he : Q.map (MulAut.conj g).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hCQ hg)
  have hEgQ : E.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [←he]
    exact map_mono hEQ
  refine ⟨hEgQ,hEgQ.trans hQT,?_⟩
  have hn := (map_mono (f := (MulAut.conj g).toMonoidHom) hQE).trans
    (E.le_normalizer_map (MulAut.conj g).toMonoidHom)
  rwa [he] at hn

/-- The actual partner normalizes the entire centralizer span. Its
intersection with M preserves E, and source ordering supplies the remaining
factor from the centralizer of U. -/
theorem PreparedChosenModule.extraspecial_kernel_span_partner_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let E := thompsonFixed T V
    let C := centralizer (U : Set G)
    Mc ≤ normalizer (conjugateSpanBy E C : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  let F := conjugateSpanBy E C
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let A := ((M ⊓ Mc).subgroupOf M).map f
  have htwo := h.maximal_overgroups_of_full_extraspecial
    hG T hempty hM hmany hJ hu hfull hex
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hne : M ≠ Mc := by
    intro he
    rw [htwo,he] at hmany
    simp at hmany
  have hproper : A ≠ ⊤ := by
    intro htop
    have hMMc : M ≤ Mc := by
      intro m hm
      have hmA : f ⟨m,hm⟩ ∈ A := htop ▸ mem_top _
      obtain ⟨a,ha,he⟩ := hmA
      have hk : a⁻¹ * (⟨m,hm⟩ : M) ∈ f.ker := by
        change f (a⁻¹ * ⟨m,hm⟩) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      have hk' : a⁻¹ * (⟨m,hm⟩ : M) ∈ (actionHom M V h.normalized).ker :=
        congrArg Subtype.val hk
      rw [actionHom_ker] at hk'
      have hh := Mc.mul_mem ha.2 (h.centralizer_le_partner T hu hk')
      change (a : G) * ((a : G)⁻¹ * m) ∈ Mc at hh
      simpa only [mul_inv_cancel_left] using hh
    exact hne (hM.1.1.eq_of_le hMc.1.1 hMMc)
  have hIE : M ⊓ Mc ≤ normalizer (E : Set G) :=
    h.extraspecial_proper_image_normalizes_fixed hG T hempty hM hmany hJ hfull hex
      (le_inf hM.1.2 hMc.2) inf_le_left hproper
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  have hmodU : localModule T Mc = U := hmod.1
  have hMcC : Mc ≤ normalizer (C : Set G) := by
    rw [hmod.2]
    exact normalizer_le_normalizer_centralizer _
  have hIF : M ⊓ Mc ≤ normalizer (F : Set G) :=
    normalizes_conjugateSpanBy E C (M ⊓ Mc) hIE (inf_le_right.trans hMcC)
  have hCF : C ≤ normalizer (F : Set G) := le_normalizer_conjugateSpanBy E C
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc
  change Mc ≤ normalizer (F : Set G)
  intro m hm
  obtain ⟨a,ha,c,hc,rfl⟩ := hord m hm
  have hcC : c ∈ C := by
    change c ∈ centralizer (U : Set G)
    rw [←hmodU]
    exact hc.2
  exact (normalizer (F : Set G)).mul_mem (hIF ⟨ha.2,ha.1⟩) (hCF hcC)

end CFSG.Quasithin.Chapter15.Section01
