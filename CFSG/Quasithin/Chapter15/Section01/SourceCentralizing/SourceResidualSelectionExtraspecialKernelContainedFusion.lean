module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContainedMarker
public import Theory.GroupTheory.WeakClosureQuotientFusion

/-!
# Pointwise correction inside the actual moved-plane centralizer

If c∈C_G(U) carries a subgroup of E back into E, the same original
J(T) centralizes both subgroups. Correcting the two conjugates of J(T)
inside C_G(U)∩C_G(Z₁ᶜ) gives n∈M∩C_G(U) with the same pointwise action
on Z₁. Unlike set fusion, this retains the literal centralizer condition.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Fusion between subgroups of the same fixed space can be corrected
pointwise while staying in the original moved-plane centralizer. -/
theorem PreparedChosenModule.extraspecial_fixed_pointwise_kernel_fusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (Z1 : Subgroup G) (hZE : Z1 ≤ thompsonFixed T V) (g : G)
    (hg : g ∈ centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G))
    (hZgE : Z1.map (MulAut.conj g).toMonoidHom ≤ thompsonFixed T V) :
    ∃ n ∈ M ⊓ centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G),
      ∀ z ∈ Z1, n*z*n⁻¹ = g*z*g⁻¹ := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let Zg := Z1.map (MulAut.conj g).toMonoidHom
  let K := C ⊓ centralizer (Zg : Set G)
  have hUE := h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  have hJE : J ≤ centralizer (thompsonFixed T V : Set G) :=
    hJ.trans (centralizer_le (inf_le_left.trans h.le_local))
  have hJC : J ≤ C := hJE.trans (centralizer_le hUE)
  have hJK : J ≤ K := le_inf hJC (hJE.trans (centralizer_le hZgE))
  have hgK : J.map (MulAut.conj g).toMonoidHom ≤ K := by
    apply le_inf
    · exact (map_mono hJC).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer hg))
    · have hJZ : J ≤ centralizer (Z1 : Set G) := hJE.trans (centralizer_le hZE)
      have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hJZ).trans
        (map_centralizer_le_centralizer_image Z1 (MulAut.conj g).toMonoidHom)
      exact hm
  obtain ⟨c,hc⟩ := Sylow.WeakClosure.normalizer_correction T J
    (sSup_le fun _ hA => hA.1) (maxJ_weakly_closed_normalizer T) K hJK g hgK
  refine ⟨(c : G)*g,⟨(source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hc,
    C.mul_mem c.property.1 hg⟩,?_⟩
  intro z hz
  have hfix := c.property.2 (g*z*g⁻¹) (mem_map_of_mem (MulAut.conj g).toMonoidHom hz)
  calc
    _ = (c : G)*(g*z*g⁻¹)*(c : G)⁻¹ := by group
    _ = g*z*g⁻¹ := by rw [←hfix,mul_inv_cancel_right]

/-- In the selected local, the same marked intersection fixes the moved
plane: its residual is contained in C_M(V), and its original Sylow fixes U. -/
theorem PreparedChosenModule.extraspecial_marked_intersection_centralizes_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      M ⊓ Mc ⊓ centralizer (ExtraspecialMarker.fixedSubgroup M V h.normalized c.X : Set G) ≤
        centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  intro c
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  obtain ⟨m,hmZ,_,_,_,_,_,_,_⟩ := c.to_marker T hM.1.2 h.normalized hex
  have htwo := h.maximal_overgroups_of_full_extraspecial
    hG T hempty hM hmany hJ hu hfull hex
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hMnot : ¬ M ≤ Mc := by
    intro hh
    have he := hM.1.1.eq_of_le hMc.1.1 hh
    rw [htwo,he] at hmany
    simp at hmany
  let I := M ⊓ Mc ⊓ centralizer (m.Z1 : Set G)
  let S := (T : Subgroup G) ⊓ centralizer (m.Z1 : Set G)
  have hSC : S ≤ centralizer (U : Set G) := by
    dsimp only [S]
    rw [hmZ]
    exact h.extraspecial_marked_sylow_centralizes_moved
      hG T hempty hM hmany hJ hfull hex c
  have hi := caseI_residual_intersection T M Mc V m.Z1 h.normalized
    (m.marked_fixed.trans inf_le_left) (inf_le_right.trans (h.centralizer_le_partner T hu))
    hMc.2 hMnot m.generates m.local_sylow (by
      rw [m.residual_card]
      exact m.prime_prime)
  have hIC : (pResidual 2 I).map I.subtype ≤ centralizer (U : Set G) := by
    rw [hi]
    exact ((map_subtype_le _).trans inf_le_right).trans (centralizer_le
      ((h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex).trans inf_le_left))
  have hSI : S ≤ I := le_inf
    (le_inf (inf_le_left.trans hM.1.2) (inf_le_left.trans hMc.2)) inf_le_right
  obtain ⟨P,hP⟩ := m.local_sylow.restrict hSI
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have he := congrArg (map I.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hP] at he
  have hb : I ≤ centralizer (U : Set G) := he.symm.le.trans (sup_le hIC hSC)
  change M ⊓ Mc ⊓ centralizer (ExtraspecialMarker.fixedSubgroup M V h.normalized c.X : Set G) ≤ _
  simpa only [I,hmZ] using hb

/-- The whole original marked partner centralizer fixes U, by pointwise
Thompson correction and the actual prime-residual intersection. -/
theorem PreparedChosenModule.extraspecial_marked_partner_centralizes_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      centralizer (ExtraspecialMarker.fixedSubgroup M V h.normalized c.X : Set G) ⊓ Mc ≤
        centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  intro mark
  let Z1 := ExtraspecialMarker.fixedSubgroup M V h.normalized mark.X
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
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
  have hCMc : C ≤ Mc := by
    rw [hmod.2]
    exact Subgroup.centralizer_le_normalizer _
  have hZfixed : Z1 ≤ E :=
    (ExtraspecialMarker.fixed_and_generation T hM.1.2 h.normalized _
      mark.fixed_thompson mark.generates).1
  have hIC := h.extraspecial_marked_intersection_centralizes_moved
    hG T hempty hM hmany hJ hu hfull hex mark
  intro g hg
  obtain ⟨a,ha,c,hc,hac⟩ :=
    source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc g hg.2
  have hcC : c ∈ C := by
    change c ∈ centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G)
    rw [←hmod.1]
    exact hc.2
  have hact (z : G) (hz : z ∈ Z1) : a*(c*z*c⁻¹)*a⁻¹=z := by
    calc
      _ = (a*c)*z*(a*c)⁻¹ := by group
      _ = g*z*g⁻¹ := by rw [hac]
      _ = z := by rw [←hg.1 z hz,mul_inv_cancel_right]
  have hZcE : Z1.map (MulAut.conj c).toMonoidHom ≤ E := by
    rintro _ ⟨z,hz,rfl⟩
    have hce : c*z*c⁻¹ = a⁻¹*z*a := by
      calc
        _ = a⁻¹*(a*(c*z*c⁻¹)*a⁻¹)*a := by group
        _ = a⁻¹*z*a := by rw [hact z hz]
    change c*z*c⁻¹ ∈ E
    rw [hce]
    simpa only [inv_inv] using le_normalizer_iff.mp hIE a⁻¹
      ⟨M.inv_mem ha.2,Mc.inv_mem ha.1⟩ z (hZfixed hz)
  obtain ⟨n,hn,hnact⟩ := h.extraspecial_fixed_pointwise_kernel_fusion
    hG T hempty hM hmany hJ hfull hex Z1 hZfixed c hcC hZcE
  have hanZ : a*n ∈ centralizer (Z1 : Set G) := by
    intro z hz
    apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
    calc
      (a*n)*z*(a*n)⁻¹ = a*(n*z*n⁻¹)*a⁻¹ := by group
      _ = a*(c*z*c⁻¹)*a⁻¹ := by rw [hnact z hz]
      _ = z := hact z hz
  have hanC : a*n ∈ C := hIC ⟨⟨M.mul_mem ha.2 hn.1,
    Mc.mul_mem ha.1 (hCMc hn.2)⟩,hanZ⟩
  have haC : a ∈ C := by
    have hh := C.mul_mem hanC (C.inv_mem hn.2)
    simpa only [mul_inv_cancel_right] using hh
  exact hac ▸ C.mul_mem haC hcC

end CFSG.Quasithin.Chapter15.Section01
