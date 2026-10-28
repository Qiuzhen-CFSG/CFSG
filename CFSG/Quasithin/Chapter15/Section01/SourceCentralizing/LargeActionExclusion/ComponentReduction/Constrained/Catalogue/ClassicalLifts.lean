module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PreimageGeneration
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PreimageGeneration
public import Theory.GroupTheory.SolvableResidual.PreimageCore
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# The literal classical residuals and their original covering maps

The parabolic residual defined in K N_S(K) equals the residual obtained
inside K. Its action kernel is solvable. The common Borel supplements
therefore give generation by the two residuals on the original marking.
Their residual core quotients are the actual SL₂ matrix group, and their
generalized Fitting subgroup is the two-core. For SL₃ and Sp₄ the original
map from K/O₂(K) is an isomorphism: the
ordinary SL₃ multiplier and the cubic-center bound handle the linear
case, including field order four; the symplectic multiplier handles Sp₄.

Source: Aschbacher--Smith 15.1.20(2), printed p.1095, and I.1.3(2),(4),
printed p.407. Membership in the original local family still requires
compatible Sylow and parabolic normalization. General Borel placement
and the rest of the constrained catalogue remain with this task.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The residual in the source normalizer is exactly the residual of the
same parabolic pulled back to K. -/
theorem normalizerParabolicResidual_eq_in_K (d : CaseIComponentData T M Mc V) (K : Subgroup G) [Group.IsPerfect K]
    (P : Subgroup (d.normalizerImage K)) :
    d.normalizerParabolicResidual K P =
      ((solvableResidual (P.comap (d.toNormalizerImage K))).map
        (P.comap (d.toNormalizerImage K)).subtype).map K.subtype := by
  let B := (d.normalizerParabolic K P).map (K ⊔ d.normalizerSylow K).subtype
  let C := (P.comap (d.toNormalizerImage K)).map K.subtype
  have hCB : C ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨inclusion le_sup_left x, ?_,rfl⟩
    exact mem_map_of_mem (d.normalizerImage K).subtype hx
  have hRC : d.normalizerParabolicResidual K P ≤ C := by
    intro x hx
    have hxK := d.normalizerParabolicResidual_le K P hx
    refine ⟨⟨x,hxK⟩,?_,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨z,hz,he⟩ := y.property
    change d.toNormalizerImage K ⟨_,hxK⟩ ∈ P
    rw [show d.toNormalizerImage K ⟨_,hxK⟩ = z from Subtype.ext he.symm]
    exact hz
  rw [d.normalizerParabolicResidual_eq, map_embedded_solvableResidual_of_hom]
  change (solvableResidual B).map B.subtype = (solvableResidual C).map C.subtype
  apply le_antisymm
  · let : Group.IsPerfect ((solvableResidual B).map B.subtype) := Group.IsPerfect.map B.subtype
    exact le_map_solvableResidual_of_isPerfect _ C (by
      rw [←d.normalizerParabolicResidual_eq]
      exact hRC)
  · exact map_solvableResidual_mono hCB

/-- The original FF action has solvable kernel on K, retaining its possible
central factor above the two-core. -/
theorem NormalizerAction.kernel_solvable {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Group.IsSolvable (d.toNormalizerImage K).ker := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : Group.IsSolvable (center (K ⧸ pCore 2 K)) :=
    Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let : Group.IsSolvable a.coreToImage.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective (a.coreToImage_ker_central hq))
  have he : (d.toNormalizerImage K).ker = a.coreToImage.ker.comap q := by
    ext x
    rfl
  rw [he]
  exact isSolvable_comap_of_solvable_ker q _

open Subgroup Theory.GroupTheory
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original symplectic FF image has exactly the two-core as kernel. -/
theorem NormalizerAction.symplectic_four_core_bijective {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F)
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    Function.Bijective a.coreToImage := by
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K)
      (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    { toMonoidHom := e.toMonoidHom.comp a.coreToImage
      surjective := e.surjective.comp a.coreToImage_surjective
      isPerfect := hq.toIsPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact a.coreToImage_ker_central hq }
  have hi := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.cover_injective (by omega) c
  exact ⟨fun _ _ hh => hi (congrArg e hh),a.coreToImage_surjective⟩

/-- The original linear-three FF image has exactly the two-core as kernel,
including the exceptional field order four. -/
theorem NormalizerAction.linear_three_core_bijective {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) (e : d.normalizerImage K ≃* SL(3,F)) :
    Function.Bijective a.coreToImage := by
  by_cases hfour : Nat.card F = 4
  · apply a.coreToImage_bijective_of_cubic_center hG h hK hq
    rw [Nat.card_congr (centerCongr e).toEquiv]
    rw [←Matrix.PSL3.projection_ker,Matrix.PSL3.card_projectionKernel,hfour]
    decide
  · let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) SL(3,F) :=
      { toMonoidHom := e.toMonoidHom.comp a.coreToImage
        surjective := e.surjective.comp a.coreToImage_surjective
        isPerfect := hq.toIsPerfect
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
          exact a.coreToImage_ker_central hq }
    let := hq
    have hc : Nat.card (center (K ⧸ pCore 2 K)) ≤ Nat.card (center SL(3,F)) := by
      have hh := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
        (by omega : Nat.card F ≠ 2) hfour c.quotientCenterEquiv
      rw [←Matrix.PSL3.card_projectionKernel,Matrix.PSL3.projection_ker] at hh
      exact Nat.le_of_dvd Nat.card_pos hh
    have he := Nat.card_congr c.quotientCenterEquiv.toEquiv
    have hj : Function.Bijective c.toMonoidHom := c.surjective.bijective_of_nat_card_le (by
      calc
        Nat.card (K ⧸ pCore 2 K) =
            Nat.card ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) *
              Nat.card (center (K ⧸ pCore 2 K)) := card_eq_card_quotient_mul_card_subgroup _
        _ ≤ Nat.card (SL(3,F) ⧸ center SL(3,F)) * Nat.card (center SL(3,F)) := by
          rw [he]
          exact Nat.mul_le_mul_left _ hc
        _ = Nat.card SL(3,F) := (card_eq_card_quotient_mul_card_subgroup _).symm)
    exact ⟨fun _ _ hh => hj.1 (congrArg e hh),a.coreToImage_surjective⟩

private theorem marked_preimage (d : CaseIComponentData T M Mc V) (K : Subgroup G)
    {E : Type*} [Group E] (e : d.normalizerImage K ≃* E) (P : Subgroup E) :
    (P.map e.symm.toMonoidHom).comap (d.toNormalizerImage K) =
      P.comap (e.toMonoidHom.comp (d.toNormalizerImage K)) := by
  ext x
  change d.toNormalizerImage K x ∈ P.map e.symm.toMonoidHom ↔ e (d.toNormalizerImage K x) ∈ P
  constructor
  · rintro ⟨y,hy,he⟩
    rw [←he]
    change e (e.symm y) ∈ P
    rw [e.apply_symm_apply]
    exact hy
  · intro hx
    exact ⟨_,hx,e.symm_apply_apply _⟩

/-- Generation by the two original linear-three parabolic residuals. -/
theorem NormalizerAction.linear_three_residuals_generate
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F]
    (e : d.normalizerImage K ≃* SL(3,F))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    d.normalizerParabolicResidual K
        ((Matrix.PSL3.LinearThree.pointParabolicSL F).map e.symm.toMonoidHom) ⊔
      d.normalizerParabolicResidual K
        ((Matrix.PSL3.LinearThree.lineParabolicSL F).map e.symm.toMonoidHom) = K := by
  let f := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hf := e.surjective.comp (d.toNormalizerImage_surjective K)
  let : Group.IsSolvable f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact a.kernel_solvable hq
  have hm := congrArg (Subgroup.map K.subtype)
    (Matrix.PSL3.LinearThree.preimage_residuals_generate f hf hF hn)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [d.normalizerParabolicResidual_eq_in_K,d.normalizerParabolicResidual_eq_in_K,
    marked_preimage,marked_preimage]
  exact hm

/-- Generation by the two original symplectic-four parabolic residuals. -/
theorem NormalizerAction.symplectic_four_residuals_generate
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    d.normalizerParabolicResidual K
        (Theory.SpecificGroups.SymplecticFour.pointParabolic.map e.symm.toMonoidHom) ⊔
      d.normalizerParabolicResidual K
        (Theory.SpecificGroups.SymplecticFour.planeParabolic.map e.symm.toMonoidHom) = K := by
  let f := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hf := e.surjective.comp (d.toNormalizerImage_surjective K)
  let : Group.IsSolvable f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact a.kernel_solvable hq
  have hm := congrArg (Subgroup.map K.subtype)
    (Theory.SpecificGroups.SymplecticFour.preimage_residuals_generate f hf hF hn)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [d.normalizerParabolicResidual_eq_in_K,d.normalizerParabolicResidual_eq_in_K,
    marked_preimage,marked_preimage]
  exact hm

private noncomputable def marked_residual_equiv
    (d : CaseIComponentData T M Mc V) (K : Subgroup G) [Group.IsPerfect K]
    {E : Type*} [Group E] (e : d.normalizerImage K ≃* E) (P : Subgroup E) :
    d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) ≃*
      solvableResidual (P.comap (e.toMonoidHom.comp (d.toNormalizerImage K))) := by
  let B := P.comap (e.toMonoidHom.comp (d.toNormalizerImage K))
  let j := K.subtype.comp B.subtype
  have he : d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) =
      (solvableResidual B).map j := by
    rw [d.normalizerParabolicResidual_eq_in_K,marked_preimage,map_map]
  exact (MulEquiv.subgroupCongr he).trans
    ((solvableResidual B).equivMapOfInjective j
      (K.subtype_injective.comp B.subtype_injective)).symm

private theorem NormalizerAction.marked_kernel
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    (hi : Function.Injective a.coreToImage)
    {E : Type*} [Group E] (e : d.normalizerImage K ≃* E) :
    IsPGroup 2 (e.toMonoidHom.comp (d.toNormalizerImage K)).ker := by
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
  have he : d.toNormalizerImage K = a.coreToImage.comp (QuotientGroup.mk' (pCore 2 K)) := rfl
  rw [he,MonoidHom.ker_comp_of_injective _ _ hi,QuotientGroup.ker_mk']
  exact pCore_isPGroup

private theorem NormalizerAction.residual_model_data
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K) (hi : Function.Injective a.coreToImage)
    {E : Type*} [Group E] [Finite E] (e : d.normalizerImage K ≃* E)
    (P J : Subgroup E) (hJ : (solvableResidual P).map P.subtype = J)
    (hfit : generalizedFitting J = pCore 2 J)
    {F : Type*} [Field F] (eq : (J ⧸ pCore 2 J) ≃* SL(2,F)) :
    generalizedFitting (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) =
        pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) ∧
      Nonempty ((d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) ⧸
        pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom))) ≃* SL(2,F)) := by
  let f := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hf := e.surjective.comp (d.toNormalizerImage_surjective K)
  have hk := a.marked_kernel hi e
  let er := marked_residual_equiv d K e P
  let em : solvableResidual P ≃* J :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ)
  have hm : generalizedFitting (solvableResidual P) = pCore 2 (solvableResidual P) := by
    rw [←map_generalizedFitting_equiv em.symm,←pCore_map_iso 2 em.symm,hfit]
  have hr := f.preimageResidual_generalizedFitting P hf hk hm
  refine ⟨?_,⟨?_⟩⟩
  · rw [←map_generalizedFitting_equiv er.symm,←pCore_map_iso 2 er.symm,hr]
  · exact (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).trans
      ((f.preimageResidualCoreEquiv P hf hk).trans
        ((QuotientGroup.congr _ _ em (pCore_map_iso 2 em)).trans eq))

/-- The two actual residual core quotients are SL₂(F), and both residuals
have generalized Fitting subgroup equal to their two-core. -/
theorem NormalizerAction.linear_three_residual_data
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (e : d.normalizerImage K ≃* SL(3,F)) :
    ∀ P ∈ ({Matrix.PSL3.LinearThree.pointParabolicSL F,
        Matrix.PSL3.LinearThree.lineParabolicSL F} : Set (Subgroup SL(3,F))),
      generalizedFitting (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) =
          pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) ∧
        Nonempty ((d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) ⧸
          pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom))) ≃* SL(2,F)) := by
  have hi := (a.linear_three_core_bijective hG h hK hq hF e).1
  intro P hP
  rcases hP with rfl | hP
  · exact a.residual_model_data hi e _ (Matrix.PSL3.LinearThree.pointLocalSL F)
      (Matrix.PSL3.LinearThree.pointParabolicSL_residual F hF)
      (Matrix.PSL3.LinearThree.pointLocalSL_generalizedFitting_eq_twoCore F)
      (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F)
  · have he : P = Matrix.PSL3.LinearThree.lineParabolicSL F := hP
    subst P
    exact a.residual_model_data hi e _ (Matrix.PSL3.LinearThree.lineLocalSL F)
      (Matrix.PSL3.LinearThree.lineParabolicSL_residual F hF)
      (Matrix.PSL3.LinearThree.lineLocalSL_generalizedFitting_eq_twoCore F)
      (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F)

/-- Both original symplectic parabolic residuals retain their rank-one
matrix quotients and characteristic-two generalized Fitting structure. -/
theorem NormalizerAction.symplectic_four_residual_data
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} [Group.IsPerfect K]
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    ∀ P ∈ ({Theory.SpecificGroups.SymplecticFour.pointParabolic,
        Theory.SpecificGroups.SymplecticFour.planeParabolic} :
          Set (Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))),
      generalizedFitting (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) =
          pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) ∧
        Nonempty ((d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom) ⧸
          pCore 2 (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom))) ≃* SL(2,F)) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hi := (a.symplectic_four_core_bijective hq hfour e).1
  intro P hP
  rcases hP with rfl | hP
  · exact a.residual_model_data hi e _ Theory.SpecificGroups.SymplecticFour.pointLocal
      (Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hF hn)
      ((Theory.SpecificGroups.SymplecticFour.pointNaturalExtension hF hn).generalizedFitting_eq (by omega))
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn)
  · have he : P = Theory.SpecificGroups.SymplecticFour.planeParabolic := hP
    subst P
    exact a.residual_model_data hi e _ Theory.SpecificGroups.SymplecticFour.planeLocal
      (Theory.SpecificGroups.SymplecticFour.planeParabolic_solvableResidual_eq hF hn)
      ((Theory.SpecificGroups.SymplecticFour.planeNaturalExtension hF hn).generalizedFitting_eq (by omega))
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
