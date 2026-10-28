module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Frattini
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# The actual central cover from the Frattini action to the moved action

The original odd Frattini action is intertwined with the omega action on
L/O₂(L), and then with the actual local component image. The strengthened
A.3.6 kernel theorem identifies its image with the quotient by the Fitting
subgroup. This is quasisimple SL₂, with defining parameter p or 5.
The surjection onto the moved image has precisely the center as kernel:
its kernel is the image of O∞(L), while the moved image has trivial radical.

All equivalences concern actual action images. The surjection retains its
equation on each original element of L.
Source: Aschbacher--Smith, 13.1.12(1), printed p.872, using A.3.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_card_dvd_of_equiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B) :
    Nat.card (fittingSubgroup A) ∣ Nat.card (fittingSubgroup B) := by
  have hle : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro N ⟨hN,hnil⟩
    apply map_le_iff_le_comap.mp
    let := hnil
    exact le_sSup ⟨hN.map _ e.surjective,Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv]
  exact card_dvd_of_le hle

/-- The literal component Frattini image is a quasisimple SL₂ cover.
The parameter restriction retains the natural and nilpotent A.3.6 branches. -/
theorem component_frattini_cover_model
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
    IsQuasisimple σ.range ∧
      ∃ q : ℕ, q.Prime ∧ 3 < q ∧ (q = p ∨ q = 5) ∧
        LocalModels.IsSL σ.range 2 q := by
  let C := radicalLocalImage (T : Subgroup G) L
  let e : XiQuotient L ≃* C := radicalLocalQuotientEquiv hL
  let q : L →* C := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hQ := uniqueness_local_quotient_sqtk hG hL.2.2
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hL.1
  have hnC : ¬ IsQuasisimple C := fun h => hn (h.of_mulEquiv e.symm)
  have hdC := hd.trans (fitting_card_dvd_of_equiv e)
  have hC : C.IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := (L ⊔ (T : Subgroup G) : Subgroup G))
    exact hL.1.map_quotient _
  have hk := (((CenterFrattiniSource.strengthened_omega_actions hQ
    (pCore_quotient_pCore_eq_bot 2) hC hc).2 hnC).2.2 p hdC).2.1
  let v := (xiPFrattiniEquivCore ho L).trans (omegaFrattiniEquiv p e)
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  let τ := omegaFrattiniAction p C
  let c := MulAut.congr v
  have he (l : L) : c (σ l) = τ (q l) := by
    apply MulEquiv.ext
    intro a
    change v (σ l (v.symm a)) = τ (q l) a
    have hx (x : XiFrattiniQuotient (XiP p L)) : v (σ l x) = τ (q l) (v x) := by
      exact (congrArg (omegaFrattiniEquiv p e)
        (xiPFrattiniEquivCore_equivariant ho L l x)).trans
          (omegaFrattiniEquiv_equivariant p e (QuotientGroup.mk' (pCore 2 L) l)
            (xiPFrattiniEquivCore ho L x))
    exact (hx (v.symm a)).trans (congrArg (τ (q l)) (v.apply_symm_apply a))
  have hm : σ.range.map c.toMonoidHom = τ.range := by
    apply le_antisymm
    · rintro _ ⟨a,⟨l,rfl⟩,rfl⟩
      exact ⟨q l,he l |>.symm⟩
    · rintro _ ⟨a,rfl⟩
      obtain ⟨l,rfl⟩ := hq a
      exact ⟨σ l,⟨l,rfl⟩,he l⟩
  let er : σ.range ≃* (C ⧸ fittingSubgroup C) :=
    ((c.subgroupMap σ.range).trans (MulEquiv.subgroupCongr hm)).trans
      (CenterFrattiniSource.omegaActionQuotientEquiv hk).symm
  have hqs : IsQuasisimple σ.range := hc.2.2.1.of_mulEquiv er.symm
  refine ⟨hqs,?_⟩
  rcases RadicalStructure.nonsimple_radical hc hnC with hnat | hnil
  · obtain ⟨r,hr,hr3,F,hF,hfin,hcard,w,eSL,hact⟩ := hnat.2
    have hsize := RadicalStructure.natural_elementary
      (show LocalModels.NaturalSL2Action C (generalizedFitting C) r from
        ⟨F,hF,hfin,hcard,w,eSL,hact⟩)
    have hdGF : p ∣ Nat.card (generalizedFitting C) := by
      rw [hnat.1]
      exact hdC
    have hdPlane : p ∣ r ^ 2 := hsize.2 ▸ hdGF
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdPlane)
    refine ⟨r,hr,hr3,Or.inl hpr.symm,F,hF,hfin,hcard,?_⟩
    exact ⟨er.trans ((QuotientGroup.quotientMulEquivOfEq hnat.1).symm.trans eSL)⟩
  · obtain ⟨F,hF,hfin,hcard,⟨eSL⟩⟩ := hnil.2.2.1
    refine ⟨5,by decide,by decide,Or.inr rfl,F,hF,hfin,hcard,?_⟩
    exact ⟨er.trans ((QuotientGroup.quotientMulEquivOfEq hnil.1).symm.trans eSL)⟩

/-- The map to the moved image is exactly the central quotient of the
actual Frattini image, and commutes with both original maps from L. -/
theorem moved_action_central_cover
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
    ∃ f : σ.range →* componentImage L, Function.Surjective f ∧
      f.ker = center σ.range ∧
      ∀ l : L, f (σ.rangeRestrict l) = (componentAction L).rangeRestrict l := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  obtain ⟨f,hf,he⟩ := moved_action_factors_frattini h hmany hL hn ho hd
  let : IsQuasisimple σ.range := (component_frattini_cover_model h.simpleQTKE hL.1.1 hn ho hd).1
  have hk : f.ker.comap σ.rangeRestrict = solvableRadical L := by
    rw [← componentAction_ker_eq_radical h hmany hL hn]
    ext l
    change f (σ.rangeRestrict l) = 1 ↔ componentAction L l = 1
    rw [he]
    exact Subtype.ext_iff
  have hkmap : f.ker = (solvableRadical L).map σ.rangeRestrict := by
    rw [← hk,map_comap_eq_self_of_surjective σ.rangeRestrict_surjective]
  have hrad : solvableRadical (componentImage L) = ⊥ := by
    rw [← map_solvableRadical_equiv (radicalEquivMovedImage h hmany hL hn),
      solvableRadical_quotient_solvableRadical,Subgroup.map_bot]
  have hcenter : center σ.range ≤ solvableRadical σ.range :=
    le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp b.property a)))
  refine ⟨f,hf,le_antisymm ?_ ?_,he⟩
  · rw [hkmap]
    exact (map_solvableRadical_le_of_surjective _ σ.rangeRestrict_surjective).trans
      IsQuasisimple.solvableRadical_le_center
  · have hh := (map_mono (f := f) hcenter).trans
      (map_solvableRadical_le_of_surjective f hf)
    rw [hrad] at hh
    exact ((Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hh))

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G]

/-- The component centralizer is the full preimage of its moved image.
This keeps the original maps on every element and the original point u. -/
theorem component_point_image_preimage
    (L : Subgroup G) (p : ℕ) (u : normalizerMoved L)
    (f : (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)).range →*
      componentImage L)
    (hf : ∀ l : L, f ((xiFrattiniAction L (XiP p L)
      (XiP_invariant p L.le_normalizer)).rangeRestrict l) =
        (componentAction L).rangeRestrict l) :
    ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)).rangeRestrict =
      (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (componentAction L).rangeRestrict).comap f := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  apply le_antisymm
  · rintro _ ⟨l,hl,rfl⟩
    exact ⟨l,hl,(hf l).symm⟩
  · intro a ha
    obtain ⟨l,rfl⟩ := σ.rangeRestrict_surjective a
    obtain ⟨k,hk,hkl⟩ := ha
    have hm : componentAction L k = componentAction L l :=
      congrArg Subtype.val (hkl.trans (hf l))
    have hv := congrArg (fun b : MulAut (normalizerMoved L) => (b u : G)) hm
    change (k : G) * (u : G) * (k : G)⁻¹ =
      (l : G) * (u : G) * (l : G)⁻¹ at hv
    have hkfix : (k : G) * (u : G) * (k : G)⁻¹ = (u : G) := by
      have hkcomm : (u : G) * (k : G) = (k : G) * (u : G) :=
        mem_centralizer_iff.mp hk u (Set.mem_singleton _)
      rw [← hkcomm,mul_inv_cancel_right]
    refine ⟨l,?_,rfl⟩
    apply mem_centralizer_iff.mpr
    intro v hvu
    obtain rfl := Set.mem_singleton_iff.mp hvu
    exact (mul_inv_eq_iff_eq_mul.mp (hv.symm.trans hkfix)).symm
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
