module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityMovementModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialPlacement

/-!
# Triality short-root movement and the source nonfusion argument

The right parabolic marking identifies its arms residual with K = O²(H)
and its unipotent subgroup with the original S. Every ambient normalizer
of K induces an automorphism of that same arms factor. The intrinsic
orbit separation proved in TrialityMovementModel therefore supplies an
original-S mover for every changed marked short-root involution.

The two source Sylow placements retain their actual conjugators. Applying
movement to the final conjugator contradicts the special-core saturation
S = Q C_{Q^g}(Z), which would fix the changed involution modulo Z(K).
This proves triality nonfusion under the remaining source premise
C_T(Z(K)) ≤ S. Neither preservation of a short-root class by an outer
automorphism nor equality between S and a conjugate of S is assumed.

The Chapter12 companion is the literal chosen-module application. The
centralizer premise, original uniqueness, exhaustive compatible comparison
and ambient recognition remain required; GlobalExit is not established.
Source: Aschbacher–Smith F.4.35, printed p.292, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem triality_conjugate_movement_transport
    {G : Type*} [Group G] (m : ℕ) (hm : 0<m)
    (R S : Subgroup G)
    (f : parabolic (binaryParameters m hm) .arms →* G) (hf : Function.Injective f)
    (hR : ((localFactor (binaryParameters m hm) .arms).subgroupOf
      (parabolic (binaryParameters m hm) .arms)).map f=R)
    (hS : ((unipotent (binaryParameters m hm)).subgroupOf
      (parabolic (binaryParameters m hm) .arms)).map f=S)
    (w : parabolic (binaryParameters m hm) .arms)
    (hw : w.val=RadicalCoordinates.LeviCommutators.short (binaryParameters m hm) rfl 2 1)
    (c : G) (hc : c∈normalizer (R : Set G)) :
    ∃ x∈S, ⁅x,c*f w*c⁻¹⁆∉(center R).map R.subtype := by
  let P := binaryParameters m hm
  let K := localFactor P .arms
  let J := parabolic P .arms
  let i : K →* J := inclusion (localFactor_le_parabolic P .arms)
  let b₀ : K →* G := f.comp i
  have hb₀ : Function.Injective b₀ := hf.comp (inclusion_injective _)
  have hrange : b₀.range=R := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hR
  let b : K ≃* R := (MonoidHom.ofInjective hb₀).trans (MulEquiv.subgroupCongr hrange)
  have hb (u : K) : (b u).val=f (i u) := rfl
  let a : MulAut K := b.trans ((R.normalizerMonoidHom ⟨c,hc⟩).trans b.symm)
  have ha (u : K) : (b (a u)).val=c*(b u).val*c⁻¹ := by
    dsimp only [a,MulEquiv.trans_apply]
    rw [b.apply_symm_apply]
    rfl
  have hwK : w.val∈K := by
    rw [hw]
    apply radical_le_localFactor P rfl .arms
    rw [RadicalCoordinates.radical_eq_descendedRootSubgroup P rfl .arms]
    exact RadicalCoordinates.LeviCommutators.short_mem P rfl .arms 2
      (by change (2 : Fin 3)≠0; decide) 1
  let v : K := ⟨w.val,hwK⟩
  have hiv : i v=w := Subtype.ext rfl
  obtain ⟨x,hx,hxv⟩ := TrialityMovement.short_root_automorphism_moved m hm a v hw
  refine ⟨(b x).val,?_,?_⟩
  · rw [hb,←hS]
    exact mem_map_of_mem f hx
  · intro hz
    have hw' : (b (a v)).val=c*f w*c⁻¹ := by rw [ha,hb,hiv]
    have hcom : (b ⁅x,a v⁆).val=⁅(b x).val,c*f w*c⁻¹⁆ := by
      rw [map_commutatorElement]
      change ⁅(b x).val,(b (a v)).val⁆=_
      rw [hw']
    obtain ⟨z,hz,he⟩ := hz
    have hz' : b ⁅x,a v⁆∈center R := (show z=b ⁅x,a v⁆ from Subtype.ext (he.trans hcom.symm)) ▸ hz
    apply hxv
    apply mem_center_iff.mpr
    intro y
    apply b.injective
    simpa only [map_mul] using mem_center_iff.mp hz' (b y)

variable {G : Type*} [Group G] [Finite G]

/-- The original S moves every ambient normalizer conjugate of the marked
triality short root, through the same right-factor map. -/
theorem Preparation.triality_short_root_conjugates_moved
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hw : (e.right w).val=RadicalCoordinates.LeviCommutators.short (binaryParameters m hm) rfl 2 1)
    (c : G) (hc : c∈normalizer (residual H : Set G)) :
    ∃ x∈sourceS L H, ⁅x,c*w.val*c⁻¹⁆∉(center (residual H)).map (residual H).subtype := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hJ : (localFactor P .arms).subgroupOf (parabolic P .arms)=solvableResidual (parabolic P .arms) := by
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic P .arms),TrialityComparison.arms_parabolic_residual P rfl]
  have hR : ((localFactor P .arms).subgroupOf (parabolic P .arms)).map f=residual H := by
    rw [hJ,show f=Y.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hS := d.triality_right_unipotent_image h hH.1.1.2 P rfl e
  have hh := triality_conjugate_movement_transport m hm (residual H) (sourceS L H)
    f hf hR hS (e.right w) hw c hc
  have hwf : f (e.right w)=w.val := by
    change (e.right.symm (e.right w)).val=w.val
    rw [e.right.symm_apply_apply]
  rwa [hwf] at hh

omit [Finite G] in
private theorem triality_core_commutator {K : Subgroup G}
    (P : Parameters) (hP : P.prime=2) (e : K ≃* localFactor P .arms) :
    ⁅K.pCoreIn 2,K.pCoreIn 2⁆≤(center K).map K.subtype := by
  have hi : ⁅pCore 2 K,pCore 2 K⁆≤center K := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_commutator,pCore_map_iso,center_map_equiv]
    rw [←map_subtype_commutator,←localFactor_arms_twoCore_center_eq_commutator P hP]
    exact arms_core_center_le_center P hP
  change ⁅(pCore 2 K).map K.subtype,(pCore 2 K).map K.subtype⁆≤_
  rw [←map_commutator]
  exact map_mono hi

private theorem saturation_fixes_point_mod_center
    {G : Type*} [Group G] {K S : Subgroup G} {v : G}
    (hv : v ∈ K.pCoreIn 2) (hc : ⁅K.pCoreIn 2,K.pCoreIn 2⁆ ≤ (center K).map K.subtype)
    (hn : S ≤ normalizer (K.pCoreIn 2 : Set G))
    (g : G) (hvg : v ∈ ((center K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (hS : S = K.pCoreIn 2 ⊔ ((K.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center K).map K.subtype : Subgroup G) : Set G))) :
    ∀ x ∈ S, ⁅x,v⁆ ∈ (center K).map K.subtype := by
  let Q := K.pCoreIn 2
  let R := Q.map (MulAut.conj g).toMonoidHom ⊓
    centralizer (((center K).map K.subtype : Subgroup G) : Set G)
  have hRN : R ≤ normalizer (Q : Set G) := (le_sup_right.trans hS.ge).trans hn
  have hRV : R ≤ centralizer ({v} : Set G) := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    obtain ⟨z,⟨k,hk,rfl⟩,he⟩ := hvg
    apply mem_centralizer_singleton_iff.mpr
    rw [←he,←map_mul,←map_mul]
    exact congrArg (MulAut.conj g).toMonoidHom (congrArg (fun t : K => t.val)
      (mem_center_iff.mp hk ⟨y,map_subtype_le _ hy⟩))
  intro x hx
  have hx' : x ∈ (Q : Set G) * (R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R hRN]
    exact hS ▸ hx
  obtain ⟨q,hq,r,hr,rfl⟩ := hx'
  have he : ⁅r,v⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hRV hr))
  rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
  exact hc (commutator_mem_commutator hq hv)


/-- The marked triality short root is not fused into Z(K), provided the
original Sylow centralizer C_T(Z(K)) lies in S. The two placements and the
movement after their actual conjugations are discharged in this theorem. -/
theorem Preparation.triality_short_root_not_fused_of_centralizer_le
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ v∈Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=RadicalCoordinates.LeviCommutators.short (binaryParameters m hm) rfl 2 1) ∧
      v∉Z ∧ orderOf v=2 ∧ ∀ g : G, v∉Z.conjBy g := by
  have hf := d.triality_right_center_fusion h hH hp m hm he
  have hPhiS := d.triality_source_frattini_le_core h hH.1.1.2 hp m hm he
  obtain ⟨e,v,hv,hmark,hvZ,hv2,_,r,s,hUQ,_,hPhiU,hUC,_⟩ :=
    d.triality_special_core_root_pair h hH hp m hm he
  obtain ⟨a⟩ := (d.triality_factor_equivs h hH.1.1.2 hp m hm e).2
  refine ⟨e,v,hv,hmark,hvZ,hv2,?_⟩
  intro g hvg
  obtain ⟨c,g',hc,hcQ,hcZ,_,hcg,hZQ,hRS,_⟩ :=
    source_special_core_placements hH.1.1.2 hPhiS hf.2.2 hCS _ hUQ hPhiU
      v hv hvZ g hvg (hUC g hvg)
  have hcK : c∈normalizer (residual H : Set G) :=
    hf.2.2 ▸ (Subgroup.centralizer_le_normalizer _ hc)
  have hg : g'∉normalizer (residual H : Set G) := by
    intro hh
    have hZg := mem_normalizer_iff_map_conj_eq.mp (hf.2.2.symm ▸ hh)
    exact hcZ (hZg ▸ hcg)
  have hsat := (d.triality_special_core_saturation h hH hp m hm he g' hg hZQ hRS).2
  have hnQ := d.S_normalizes_right.trans (normalizer_le_normalizer_characteristic_image
    (residual H) (pCore 2 (residual H)))
  have hfixed := saturation_fixes_point_mod_center hcQ
    (triality_core_commutator (binaryParameters m hm) rfl a) hnQ g' hcg hsat
  obtain ⟨w,hwv,hw⟩ := hmark
  obtain ⟨x,hx,hxv⟩ := d.triality_short_root_conjugates_moved h hH hp m hm e w hw c hcK
  rw [hwv] at hxv
  exact hxv (hfixed x hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
