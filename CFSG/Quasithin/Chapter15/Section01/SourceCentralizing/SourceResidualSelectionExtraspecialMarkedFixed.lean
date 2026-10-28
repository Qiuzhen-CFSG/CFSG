module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedFixedLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContainedFusion

/-!
# The actual marked centralizer is the full fixed-space centralizer

The original noncentral cubic fixed plane Z₁ complements the original
Thompson moved plane U inside E. Pointwise Thompson fusion places its
partner centralizer M_Z inside C_G(U), hence M_Z = C_G(E). Since T
normalizes E, it normalizes this same marked centralizer. No global
residual-centralization conclusion enters this argument.

Source: Aschbacher--Smith 15.1.16--18, printed pp.1092--1093.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- The marked plane and moved plane form a direct sum inside the literal
ambient Thompson fixed subgroup. -/
theorem PreparedChosenModule.extraspecial_marked_fixed_subgroups
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∀ c : ExtraspecialMarker.ImageMarking T M V h.normalized,
      ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ⊔
          ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = thompsonFixed T V ∧
        ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ⊓
          ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = ⊥ := by
  let := h.elementary
  intro c
  let ρ := imageRepresentation M V h.normalized
  let P := pResidual 2 (internalActionImage M V h.normalized)
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.normalized).rangeRestrict
  let W := fixedSpace ρ (c.X.map P.subtype)
  let B := subspaceCommutator ρ ⊤ R
  let Z1 := ExtraspecialMarker.fixedSubgroup M V h.normalized c.X
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  obtain ⟨hd,hs⟩ := h.extraspecial_marked_fixed_direct_sum
    hG T hempty hM hmany hJ hfull hex c
  change Disjoint W B at hd
  change fixedSpace ρ R = W ⊔ B at hs
  have hJM := (ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2
  have he := ambientSpace_fixed h.normalized hJM
  change ambientSpace V (fixedSpace ρ R) = thompsonFixed T V at he
  have hm := ambientSpace_moved h.normalized h.le_selected hJM
  change ambientSpace V B = U at hm
  have hz : ambientSpace V W = Z1 := rfl
  have hZV : Z1 ≤ V := map_subtype_le _
  have hUV : U ≤ V := hm ▸ map_subtype_le _
  have hsum : Z1 ⊔ U = thompsonFixed T V := by
    apply le_antisymm
    · apply sup_le
      · intro z hz1
        rw [←he]
        obtain ⟨w,hw,rfl⟩ := hz1
        exact ⟨w,hs.symm ▸ (show Additive.ofMul w ∈ W ⊔ B from Submodule.mem_sup_left hw),rfl⟩
      · intro z hzu
        rw [←hm] at hzu
        rw [←he]
        obtain ⟨w,hw,rfl⟩ := hzu
        exact ⟨w,hs.symm ▸ (show Additive.ofMul w ∈ W ⊔ B from Submodule.mem_sup_right hw),rfl⟩
    · intro z hze
      rw [←he] at hze
      obtain ⟨w,hw,rfl⟩ := hze
      change Additive.ofMul w ∈ fixedSpace ρ R at hw
      rw [hs] at hw
      obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hw
      have hx' : (x.toMul : G) ∈ Z1 := mem_map_of_mem V.subtype hx
      have hy' : (y.toMul : G) ∈ U := hm ▸ mem_map_of_mem V.subtype hy
      have heq := congrArg (fun a : Additive V => (a.toMul : G)) hxy
      change (x.toMul : G) * y.toMul = w at heq
      change (w : G) ∈ Z1 ⊔ U
      rw [←heq]
      exact (Z1 ⊔ U).mul_mem ((show Z1 ≤ Z1 ⊔ U from le_sup_left) hx')
        ((show U ≤ Z1 ⊔ U from le_sup_right) hy')
  refine ⟨hsum,bot_unique ?_⟩
  intro z hz1
  let v : V := ⟨z,hZV hz1.1⟩
  have hvW : Additive.ofMul v ∈ W := (mem_ambientSpace W v).mp (hz.symm ▸ hz1.1)
  have hvB : Additive.ofMul v ∈ B := (mem_ambientSpace B v).mp (hm.symm ▸ hz1.2)
  exact congrArg (fun a : Additive V => (a.toMul : G))
    (Submodule.disjoint_def.mp hd _ hvW hvB)

/-- Pointwise Thompson fusion and the marked direct sum identify the actual
partner marked centralizer with C_G(E), and hence give its T-normality. -/
theorem PreparedChosenModule.extraspecial_marked_partner_eq_fixed_centralizer
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
      let MZ := centralizer (ExtraspecialMarker.fixedSubgroup M V h.normalized c.X : Set G) ⊓ Mc
      MZ = centralizer (thompsonFixed T V : Set G) ∧
        (T : Subgroup G) ≤ normalizer (MZ : Set G) := by
  let := h.elementary
  intro c
  let Z1 := ExtraspecialMarker.fixedSubgroup M V h.normalized c.X
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let MZ := centralizer (Z1 : Set G) ⊓ Mc
  have hs := (h.extraspecial_marked_fixed_subgroups hG T hempty hM hmany hJ hfull hex c).1
  change Z1 ⊔ U = E at hs
  have hc := h.extraspecial_marked_partner_centralizes_moved
    hG T hempty hM hmany hJ hu hfull hex c
  change MZ ≤ centralizer (U : Set G) at hc
  have hCU : centralizer (U : Set G) ≤ Mc := by
    rw [(h.extraspecial_partner_module_and_normalizer hG T hempty hM hmany hJ hu hfull hex).2]
    exact Subgroup.centralizer_le_normalizer _
  have heq : MZ = centralizer (E : Set G) := by
    apply le_antisymm
    · apply le_centralizer_iff.mpr
      rw [←hs]
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp hc)
    · have hZE : Z1 ≤ E := hs ▸ le_sup_left
      have hUE : U ≤ E := hs ▸ le_sup_right
      exact le_inf (centralizer_le hZE) ((centralizer_le hUE).trans hCU)
  change MZ = centralizer (E : Set G) ∧ (T : Subgroup G) ≤ normalizer (MZ : Set G)
  refine ⟨heq,?_⟩
  rw [heq]
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  exact hTE.trans (normalizer_le_normalizer_centralizer _)

end CFSG.Quasithin.Chapter15.Section01
