module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SeedCubicAction
public import Theory.Representation.InvertedCubicTensor.NaturalTensorFree
public import Theory.Representation.BinaryConjugationSection.FixedPointFree
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The opposite residual when the original intersection is the seed

The natural S₃ action on O₂(I₂)/E and its faithful action on the seed
have a common cubic with no nonidentity fixed point. Once E=V, this proves
R=[R,O²(I₂)] for the literal R=O₂(I₂), and identifies both O²(I₂) and its
two-core with the original source residual and R. The proof uses the
binary generation formulas, without a solvability or orthogonal-plus
assumption on the terminal action.

This extends the earlier parabolic residual calculation to the normalized
A₅ branch, where the seed intersection has been independently proved.
Source: Aschbacher–Smith 12.8.9–11, 14.2.16 and 14.3.15,
printed pp.852–854,986,994.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor Theory.GroupTheory
open scoped TensorProduct IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem parabolic_residual_core_structure_of_seed_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (dg : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hE : F.E g = rankTwoSeed T M) :
    (pResidual 2 (F.I₂ (sourceResidual M Mc))).map (F.I₂ (sourceResidual M Mc)).subtype =
      sourceResidual M Mc ∧
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 =
      ⁅(F.I₂ (sourceResidual M Mc)).pCoreIn 2,sourceResidual M Mc⁆ ∧
    (sourceResidual M Mc).pCoreIn 2=(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
    ∃ c:G,c∈sourceResidual M Mc ∧ orderOf c=3 ∧
      (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊓centralizer ({c}:Set G)=⊥ := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,hgen,_,hIG,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  let e'' := e₀
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e'' hcore hindex
  let := F.binary_source_E_normal_in_core L h.L_normalizes_seed g hgP hgen.symm hcomm
  let := F.binary_source_quotient_elementary L h.L_normalizes_seed g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  obtain ⟨σ,d,_,hfinite,⟨j,hj⟩,hfixed⟩ :=
    F.binary_natural_quotient L h.L_normalizes_seed g hgP hfactor hPH hgen.symm e'' hcore hindex hcomm hsquare
  let := hfinite
  let I := F.I₂ L
  let D := (pResidual 2 I).map I.subtype
  have hDL : D=L := by
    change (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype=L
    rw [(F.binary_residual_supplement (by decide) L hsquare hfactor).2,F.P_rankTwo]
    exact embedded_pResidual_join_pGroup L (T:Subgroup G)
      ((pResidual_eq_top_iff 2 L).mp h.L_residual) T.isPGroup' h.sylow_normalizes_L
  let π := F.binaryCoreProjection L e''
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 I) (e''.symm s)
    exact ⟨i,by rw [F.binaryCoreProjection_apply,hi,e''.apply_symm_apply]⟩
  have hc : cubic∈pResidual 2 S₃ := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (by decide +kernel : cubic^3=1)))
  have hic : cubic∈(pResidual 2 I).map π := by
    rw [map_pResidual_of_surjective 2 π hπ]
    exact hc
  obtain ⟨i,hi,hic⟩ := mem_map.mp hic
  have hiD : (i:G)∈D := mem_map_of_mem I.subtype hi
  have hVN : I≤normalizer (rankTwoSeed T M:Set G) := by simpa only [Gi,F.last] using hIG
  let α : MulAut (rankTwoSeed T M) := (rankTwoSeed T M).normalizerMonoidHom ⟨i,hVN i.property⟩
  have hfree : MonoidHom.FixedPointFree α.toMonoidHom := by
    intro v hv
    apply Subtype.ext
    exact binary_core_cubic_seed_fixed_free F L e'' hIG hcore i hic v v.property
      (congrArg Subtype.val hv)
  have hRfree (r:G) (hr:r∈(F.I₂ L).pCoreIn 2) (hfix:(i:G)*r*(i:G)⁻¹=r) : r=1 := by
    let rR : (F.I₂ L).pCoreIn 2 := ⟨r,hr⟩
    have he := d.equivariant i rR
    have hri : (⟨(i:G)*r*(i:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized i.property) r).mp hr⟩:(F.I₂ L).pCoreIn 2)=rR :=
      Subtype.ext hfix
    rw [hri] at he
    change (d.coordinates rR).toAdd=σ (π i) (d.coordinates rR).toAdd at he
    rw [hic] at he
    have hz := cubic_fixed_zero_of_natural_tensor σ j hj (d.coordinates rR).toAdd he.symm
    have hrE : r∈F.E g := (d.coordinates_eq_one_iff rR).mp
      (Multiplicative.toAdd.injective hz)
    exact binary_core_cubic_seed_fixed_free F L e'' hIG hcore i hic r (hE ▸ hrE) hfix
  have hi3 : (i:G)^3∈(F.I₂ L).pCoreIn 2 := by
    have hp : π (i^3)=1 := by rw [map_pow,hic]; decide +kernel
    have he : QuotientGroup.mk' (pCore 2 I) (i^3)=1 := by
      apply e''.injective
      change F.binaryCoreProjection L e'' (i^3)=1 at hp
      rw [F.binaryCoreProjection_apply] at hp
      simpa only [map_one] using hp
    have hm : i^3∈pCore 2 I := (QuotientGroup.eq_one_iff _).mp he
    exact mem_map_of_mem I.subtype hm
  have hiPow : (i:G)^3=1 := hRfree _ hi3 (by group)
  have hiNe : (i:G)≠1 := by
    intro hh
    have hi1 : i=1 := Subtype.ext hh
    rw [hi1,map_one] at hic
    exact (by decide +kernel : (1:S₃)≠cubic) hic
  have hiOrder : orderOf (i:G)=3 := (orderOf_eq_prime_iff (p:=3)).mpr ⟨hiPow,hiNe⟩
  have hC : (F.I₂ L).pCoreIn 2⊓centralizer ({(i:G)}:Set G)=⊥ := by
    apply bot_unique
    intro r hr
    apply mem_bot.mpr
    apply hRfree r hr.1
    have hh := hr.2 (i:G) (Set.mem_singleton _)
    calc (i:G)*r*(i:G)⁻¹=r*(i:G)*(i:G)⁻¹ := congrArg (fun a:G=>a*(i:G)⁻¹) hh
         _=r := by group
  have hVR : rankTwoSeed T M≤(F.I₂ L).pCoreIn 2 := by
    simpa only [hE] using d.kernel_le
  have hID : ⁅I,D⁆≤D := le_normalizer_iff_commutator_le_right.mp (le_normalizer_embedded_pResidual 2 I)
  have hVC : rankTwoSeed T M≤⁅(F.I₂ L).pCoreIn 2,D⁆ := by
    intro v hv
    obtain ⟨w,hw⟩ := hfree.commutatorMap_surjective (⟨v,hv⟩:rankTwoSeed T M)
    have hh : (w:G)/((α w:G))∈⁅(F.I₂ L).pCoreIn 2,D⁆ := by
      have hm : (w:G)/((α w:G))=(w:G)*(i:G)*(w:G)⁻¹*(i:G)⁻¹ := by
        change (w:G)/((i:G)*(w:G)*(i:G)⁻¹)=_
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        group
      rw [hm]
      exact commutator_mem_commutator (hVR w.property) hiD
    have he : (w:G)/(α w:G)=v := congrArg Subtype.val hw
    exact he ▸ hh
  have hRC : (F.I₂ L).pCoreIn 2=⁅(F.I₂ L).pCoreIn 2,D⁆ := by
    have he := d.section_eq_commutator_sup_of_fixedPointFree D (map_subtype_le _) i hiD
      (by
        intro v hv
        change σ (π i) v=v at hv
        rw [hic] at hv
        exact cubic_fixed_zero_of_natural_tensor σ j hj v hv)
    exact he.trans (sup_of_le_left (show F.E g≤⁅(F.I₂ L).pCoreIn 2,D⁆ from by rwa [hE]))
  have hR : (F.I₂ L).pCoreIn 2≤D := by
    exact hRC.le.trans ((commutator_mono d.section_le le_rfl).trans hID)
  have hc := pCoreIn_embedded_pResidual_eq_of_core_le 2 I hR
  change D.pCoreIn 2=(F.I₂ L).pCoreIn 2 at hc
  exact ⟨hDL,by simpa only [hDL] using hRC,by simpa only [hDL] using hc,
    i,(show (i:G)∈L from hDL.le hiD),hiOrder,hC⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
