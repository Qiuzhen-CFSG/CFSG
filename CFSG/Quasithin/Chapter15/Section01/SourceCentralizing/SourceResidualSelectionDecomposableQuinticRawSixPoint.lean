module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixGeometry
public import Theory.GroupTheory.PPerfectCentralLift
-- Intentional reuse of the intrinsic ordinary-A6 fixed-line calculation.
-- No CaseIComponentData record is constructed or passed to a public theorem.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixGeometry

/-! An automorphism of an ordinary A6 block fixing a full Sylow subgroup
pointwise has a maximal fixed subgroup. The native fixed-line calculation
first gives fixation modulo the full center. Two-perfect lift rigidity and
the same Sylow supplement remove that central error. Applied to an original
central involution, singleton-partner control identifies a maximal original
marked intersection. The full block module need not have trivial center. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem fixed_center_lift {A : Type*} [Group A] [Finite A]
    (hp : IsPGroup 2 (center A)) (P : Sylow 2 A) (a : MulAut A)
    (ha : ∀ x ∈ P, a x = x) :
    ((QuotientGroup.mk' (center A)).comp a.toMonoidHom).eqLocus
      (QuotientGroup.mk' (center A)) = a.toMonoidHom.eqLocus (MonoidHom.id A) := by
  let q := QuotientGroup.mk' (center A)
  let F := (q.comp a.toMonoidHom).eqLocus q
  have hPF : (P : Subgroup A) ≤ F := by
    intro x hx
    change q (a x) = q x
    rw [ha x hx]
  let Q := P.subtype hPF
  have hQ : (Q : Subgroup F).map F.subtype = (P : Subgroup A) := by
    simp only [Q,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPF]
  let f₁ := a.toMonoidHom.comp F.subtype
  let f₂ := F.subtype
  let R := pResidual 2 F
  have hr : f₁.comp R.subtype = f₂.comp R.subtype := by
    apply (isPPerfect_pResidual 2).hom_eq_of_comp_eq_of_central_pGroup_kernel q
      (by rw [QuotientGroup.ker_mk'])
      (hp.of_equiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center A))).symm)
    apply MonoidHom.ext
    intro x
    exact x.val.property
  have hRF : R ≤ f₁.eqLocus f₂ := by
    intro x hx
    exact DFunLike.congr_fun hr ⟨x,hx⟩
  have hQF : (Q : Subgroup F) ≤ f₁.eqLocus f₂ := by
    intro x hx
    apply ha
    have hh := mem_map_of_mem F.subtype hx
    rw [hQ] at hh
    exact hh
  have htop : (⊤ : Subgroup F) ≤ f₁.eqLocus f₂ :=
    (pResidual_sup_sylow_eq_top Q).symm ▸ sup_le hRF hQF
  apply le_antisymm
  · intro x hx
    exact htop (show (⟨x,hx⟩ : F) ∈ ⊤ from mem_top _)
  · intro x hx
    change q (a x) = q x
    exact congrArg q hx

/-- Pointwise fixation of a full Sylow in the ordinary A6 block has a maximal
fixed subgroup, even when the block's full central layer is nontrivial. -/
theorem raw_six_sylow_fixer_coatom
    {A : Type*} [Group A] [Finite A] (hb : IsAlternatingBlock A 6)
    (P : Sylow 2 A) (a : MulAut A) (ha : a ≠ 1)
    (hP : ∀ x ∈ P, a x = x) : IsCoatom (a.toMonoidHom.eqLocus (MonoidHom.id A)) := by
  let : CommGroup (center A) := IsMulCommutative.instCommGroup
  have hcent : center A ≤ pCore 2 A := by
    rw [←hb.2.1.fitting]
    exact (show center A ≤ fittingSubgroup A from le_sSup ⟨inferInstance,inferInstance⟩).trans
      (fitting_le_generalizedFitting A)
  have he := fixed_center_lift (pCore_isPGroup.to_le hcent) P a hP
  obtain ⟨J,hJ,hfix⟩ := CaseIComponentData.SixGeometry.six_fixer_parabolic hb P a ha
    (fun x hx => by rw [hP x hx,mul_inv_cancel]; exact one_mem _)
  have hJF : J ≤ a.toMonoidHom.eqLocus (MonoidHom.id A) := by
    rw [←he]
    intro x hx
    change QuotientGroup.mk' (center A) (a x) = QuotientGroup.mk' (center A) x
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hfix x hx)
  have hproper : a.toMonoidHom.eqLocus (MonoidHom.id A) ≠ ⊤ := by
    intro ht
    apply ha
    apply MulEquiv.ext
    intro x
    exact ht.ge (show x ∈ ⊤ from mem_top _)
  exact ((hJ.le_iff_eq hproper).mp hJF) ▸ hJ

variable {G : Type*} [Group G] [Finite G]

/-- A noncentral original central involution forces the marked intersection
of the ordinary A6 block to be a maximal subgroup of that same block. -/
theorem PreparedChosenModule.raw_six_marked_coatom
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (hb : IsAlternatingBlock L 6) :
    IsCoatom (((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L).subgroupOf L) := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  have hZR := (h.raw_component_thompson hG T hM hJ hu hZ hL
    hi.quasisimple hi.fitting hi.outside houtM).2.2.2.2
  have hMc : centralizer (centralInvolutions T : Set G) ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  have hn : ¬ centralInvolutions T ≤ centralizer (L : Set G) := by
    intro hc
    exact hi.outside (le_inf hL.1 ((le_centralizer_iff.mp hc).trans hMc))
  obtain ⟨z,hz,hzc⟩ := SetLike.not_le_iff_exists.mp hn
  have hz1 : z ≠ 1 := fun he => hzc (he ▸ one_mem _)
  let a := L.normalizerMonoidHom ⟨z,(hZR hz).2⟩
  have ha : a ≠ 1 := by
    intro he
    apply hzc
    intro x hx
    have hh := congrArg (fun b : MulAut L => (b ⟨x,hx⟩ : G)) he
    change z*x*z⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hL.2
  have hfix : ∀ x ∈ P, a x = x := by
    intro x hx
    apply Subtype.ext
    change z*(x : G)*z⁻¹=x
    have hxT := (hP ▸ mem_map_of_mem L.subtype hx).1.1
    rw [←centralInvolutions_le_centralizer_sylow T hz x hxT,mul_inv_cancel_right]
  have hc := raw_six_sylow_fixer_coatom hb P a ha hfix
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    have hzp : IsPGroup 2 (zpowers z) :=
      T.isPGroup'.to_le ((zpowers_le.mpr hz).trans (centralInvolutions_le_sylow T))
    have hh := centralizer_le_of_unique_twoLocal hzp
      (fun he => hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ mem_zpowers z))
      ((centralizer_le (show (zpowers z : Set G) ⊆ centralInvolutions T from
        zpowers_le.mpr hz)).trans (Subgroup.centralizer_le_normalizer _))
      (M := Mc) (by
        intro K hK hCK
        exact Set.mem_singleton_iff.mp (hu ▸ (show K ∈ maximalTwoLocalOvergroups
          (centralizer (centralInvolutions T : Set G)) from ⟨hK,hCK⟩)))
    apply le_trans ?_ hh
    rw [le_centralizer_iff,zpowers_le]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hcN : a.toMonoidHom.eqLocus (MonoidHom.id L) ≤ (N ⊓ L).subgroupOf L := by
    intro x hx
    refine ⟨⟨hL.1 x.property,hCz ?_⟩,x.property⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val hx
    change z*(x : G)*z⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hproper : (N ⊓ L).subgroupOf L ≠ ⊤ := by
    intro ht
    exact hi.outside fun x hx => (ht.ge (show (⟨x,hx⟩ : L) ∈ ⊤ from mem_top _)).1
  exact ((hc.le_iff_eq hproper).mp hcN) ▸ hc

end CFSG.Quasithin.Chapter15.Section01
