module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.G2
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Construction
public import Theory.GroupTheory.CentralInvolutionMarking
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Original-source rigidity for the derived binary G₂ parabolic

The shared involution of a quaternion–cyclic core is its unique nontrivial
square, so every core automorphism fixes it. Quotienting by this involution
makes the core abelian. In a characteristic-two overgroup containing the
same Sylow two-subgroup, the source centralizer chain therefore identifies
the two cores. The actual local residual fills the intrinsic residual
of the core automorphism group. Its centralizer kernel lies in the core,
and the Sylow supplement then gives equality of the local groups.

For the actual first parabolic of G₂(2)′, the computed core and residual
supply these hypotheses. The original central-involution marking fixes
its image without an additional marking assumption. Original 14.2.3 and
the source centralizer decomposition consequently give H = Mc and M = YT.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal

private theorem model_involution_fixed (a : MulAut QuaternionCyclic.Model) :
    a (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z) =
      QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z := by
  rw [← QuaternionCyclic.r_sq, map_pow]
  apply QuaternionCyclic.square_eq_involution
  intro h
  have hr : QuaternionCyclic.r ^ 2 = 1 := a.injective (by simpa using h)
  have hd := orderOf_dvd_of_pow_eq_one hr
  rw [QuaternionCyclic.r_order] at hd
  norm_num at hd

/-- The distinguished central involution of a quaternion–cyclic two-core. -/
@[expose] def quaternionCyclicCoreMark {A : Type*} [Group A]
    (e : pCore 2 A ≃* QuaternionCyclic.Model) : A :=
  (e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z) : pCore 2 A)

theorem quaternionCyclicCoreMark_properties {A : Type*} [Group A]
    (e : pCore 2 A ≃* QuaternionCyclic.Model) :
    quaternionCyclicCoreMark e ∈ center A ∧ orderOf (quaternionCyclicCoreMark e) = 2 := by
  constructor
  · apply mem_center_iff.mpr
    intro a
    have hm := model_involution_fixed (MulAut.congr e (MulAut.conjNormal a))
    have he := congrArg e.symm hm
    have hfix : MulAut.conjNormal a
        (e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z)) =
          e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z) := by
      change e.symm (e (MulAut.conjNormal a
        (e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z)))) = _ at he
      simpa only [e.symm_apply_apply] using he
    have h := congrArg Subtype.val hfix
    change a * quaternionCyclicCoreMark e * a⁻¹ = quaternionCyclicCoreMark e at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · change orderOf ((pCore 2 A).subtype
      (e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z))) = 2
    rw [orderOf_injective (pCore 2 A).subtype (pCore 2 A).subtype_injective,
      e.symm.orderOf_eq, ← QuaternionCyclic.r_sq, orderOf_pow,
      QuaternionCyclic.r_order]
    decide

private theorem core_le_embedded_core {A D : Type*} [Group A] [Group D]
    (i : A →* D) (hi : Function.Injective i)
    (S : Sylow 2 D) (hS : (S : Subgroup D) ≤ i.range) :
    pCore 2 D ≤ (pCore 2 A).map i := by
  have hQr : pCore 2 D ≤ i.range := (pCore_isPGroup.le_sylow_of_normal S).trans hS
  have hpre : (pCore 2 D).comap i ≤ pCore 2 A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  simpa only [map_comap_eq_self hQr] using map_mono (f := i) hpre

private theorem core_image_abelian
    {A D : Type*} [Group A] [Group D]
    (e : pCore 2 A ≃* QuaternionCyclic.Model) (i : A →* D)
    (Z : Subgroup D) [Z.Normal] (hz : i (quaternionCyclicCoreMark e) ∈ Z) :
    IsMulCommutative (((pCore 2 A).map i).map (QuotientGroup.mk' Z)) := by
  have htable : ∀ x y : QuaternionCyclic.Model,
      ⁅x,y⁆ = 1 ∨ ⁅x,y⁆ = QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z := by
    decide +kernel
  have hcomm (a b : pCore 2 A) : i (⁅(a:A),(b:A)⁆) ∈ Z := by
    rcases htable (e a) (e b) with hh | hh
    · have he : ⁅a,b⁆ = 1 := e.injective (by simpa only [map_commutatorElement, map_one] using hh)
      change i ((⁅a,b⁆ : pCore 2 A) : A) ∈ Z
      rw [he]
      exact (map_one i).symm ▸ Z.one_mem
    · have he : ⁅a,b⁆ = e.symm (QuaternionCyclic.quaternionEmbedding QuaternionCyclic.z) := by
        apply e.injective
        simpa only [map_commutatorElement, e.apply_symm_apply] using hh
      change i ((⁅a,b⁆ : pCore 2 A) : A) ∈ Z
      rw [he]
      exact hz
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  obtain ⟨_,⟨a,ha,rfl⟩,rfl⟩ := ha
  obtain ⟨_,⟨b,hb,rfl⟩,rfl⟩ := hb
  change (QuotientGroup.mk' Z (i a)) * (QuotientGroup.mk' Z (i b)) =
    (QuotientGroup.mk' Z (i b)) * (QuotientGroup.mk' Z (i a))
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv, mul_inv_rev, ← map_mul, ← map_inv,
    commutatorElement_def, mul_assoc] using hcomm ⟨a,ha⟩ ⟨b,hb⟩

/-- A Sylow-preserving overgroup centralizing the source involution equals
the quaternion–cyclic local group when its residual realizes the intrinsic
residual automorphisms of its core. -/
theorem quaternionCyclic_overgroup_rigidity
    {A D : Type*} [Group A] [Finite A] [Group D] [Finite D]
    (e : pCore 2 A ≃* QuaternionCyclic.Model)
    (hres : (pResidual 2 A).map (MulAut.conjNormal (H := pCore 2 A)) =
      pResidual 2 (MulAut (pCore 2 A)))
    (i : A →* D) (hi : Function.Injective i)
    (S : Sylow 2 D) (hS : (S : Subgroup D) ≤ i.range)
    (hz : i (quaternionCyclicCoreMark e) ∈ center D)
    (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) : i.range = ⊤ := by
  let Z := zpowers (i (quaternionCyclicCoreMark e))
  have hZ : Z ≤ center D := zpowers_le.mpr hz
  let : Z.Normal := ⟨fun a ha b => by
    simpa only [mem_center_iff.mp (hZ ha) b, mul_inv_cancel_right] using ha⟩
  have hZQ : Z ≤ pCore 2 D := (hZ.trans (center_le_centralizer _)).trans hc
  let : IsMulCommutative (((pCore 2 A).map i).map (QuotientGroup.mk' Z)) :=
    core_image_abelian e i Z (mem_zpowers _)
  have hQ : pCore 2 D = (pCore 2 A).map i :=
    core_eq_of_abelian_quotient Z _ _ hZQ (core_le_embedded_core i hi S hS)
      (centralizer_image_pCore_le_of_central_quotient Z hZ hc)
  let eQ : pCore 2 A ≃* pCore 2 D :=
    ((pCore 2 A).equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hQ.symm)
  let ρ : D →* MulAut (pCore 2 D) := MulAut.conjNormal
  have heQ (x : pCore 2 A) : (eQ x : D) = i x := rfl
  have hact : ρ.comp i = (MulAut.congr eQ).toMonoidHom.comp
      (MulAut.conjNormal (H := pCore 2 A)) := by
    ext a x
    obtain ⟨y,rfl⟩ := eQ.surjective x
    change i a * (eQ y : D) * (i a)⁻¹ =
      (eQ (MulAut.conjNormal a (eQ.symm (eQ y))) : D)
    rw [eQ.symm_apply_apply, heQ, heQ]
    change i a * i (y:A) * (i a)⁻¹ = i (a * (y:A) * a⁻¹)
    simp only [map_mul, map_inv]
  have himage : (pResidual 2 A).map (ρ.comp i) = pResidual 2 (MulAut (pCore 2 D)) := by
    rw [hact, ← map_map, hres, map_pResidual]
  have hri : pResidual 2 (MulAut (pCore 2 D)) ≤ i.range.map ρ := by
    rw [← himage, ← map_map]
    exact map_mono (map_le_range _ _)
  have hker : ρ.ker ≤ i.range := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact hc.trans (hQ ▸ map_le_range _ _)
  have hR : pResidual 2 D ≤ i.range := by
    have hh := map_le_map_iff.mp ((map_pResidual_le 2 ρ).trans hri)
    simpa only [sup_eq_left.mpr hker] using hh
  exact top_unique ((pResidual_sup_sylow_eq_top S) ▸ sup_le hR hS)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair Parabolics Stellmacher

/-- The G₂(2)′ row of original 14.2.21. The ordinary first-parabolic
isomorphism suffices: its central involution is forced to be the source mark. -/
theorem source_g2_derived_rigidity
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (d : derivedFirst ≃* H) :
    H = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) := by
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc : H ≤ Mc := hMc ▸
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTMc : (T : Subgroup G) ≤ Mc := hTH.trans hHMc
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1,hTMc⟩)
  let j := quaternionCyclicCoreMark g2_derived_first_core_model
  have hj := quaternionCyclicCoreMark_properties g2_derived_first_core_model
  have hmark : zpowers (d j : G) = centralInvolutions T := by
    apply central_involution_marking T H hTH hZ (d j)
    · exact (MulEquivClass.apply_mem_center_iff d).mpr hj.1
    · exact (d.orderOf_eq j).trans hj.2
  let i : derivedFirst →* Mc := (inclusion hHMc).comp d.toMonoidHom
  have hi : Function.Injective i := (inclusion_injective hHMc).comp d.injective
  have hr : i.range = H.subgroupOf Mc := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact (d a).property
    · intro hx
      obtain ⟨a,ha⟩ := d.surjective ⟨x,hx⟩
      exact ⟨a,Subtype.ext (congrArg (fun y : H => (y:G)) ha)⟩
  have hSi : ((T.subtype hTMc) : Subgroup Mc) ≤ i.range := by
    rw [hr, Sylow.coe_subtype]
    intro x hx
    exact hTH hx
  have hjMc : i j ∈ center Mc := by
    apply mem_center_iff.mpr
    intro g
    apply Subtype.ext
    have hg : (g:G) ∈ centralizer (centralInvolutions T : Set G) := hMc ▸ g.property
    exact (hg _ (hmark ▸ mem_zpowers _)).symm
  have htop := quaternionCyclic_overgroup_rigidity g2_derived_first_core_model
    g2_derived_residual_automorphisms i hi (T.subtype hTMc) hSi hjMc hc
  have heq : H = Mc := by
    apply le_antisymm hHMc
    intro g hg
    exact show (⟨g,hg⟩ : Mc) ∈ H.subgroupOf Mc from
      hr ▸ htop.ge (mem_top _)
  have hcardH : Nat.card H = 96 := (Nat.card_congr d.toEquiv).symm.trans card_derivedFirst
  have hcardQ : Nat.card (pCore 2 H) = 16 := by
    rw [← pCore_map_iso 2 d,
      ← Nat.card_congr ((pCore 2 derivedFirst).equivMapOfInjective d.toMonoidHom d.injective).toEquiv,
      Nat.card_congr g2_derived_first_core_model.toEquiv, QuaternionCyclic.card_model]
  have hquot : Nat.card (H ⧸ pCore 2 H) = 6 := by
    have hh := (pCore 2 H).card_mul_index
    change Nat.card (pCore 2 H) * Nat.card (H ⧸ pCore 2 H) = Nat.card H at hh
    rw [hcardH,hcardQ] at hh
    omega
  have hint : H ⊓ M = (T : Subgroup G) := by
    have hh := (sylow_normalizer_small_core_quotient (T.subtype hTH) (Or.inl hquot)).2
      (M.subgroupOf H) (fun x hx => hM.1.2 hx) (lt_top_iff_ne_top.mpr (by
        intro ht
        apply hH.1.2
        intro x hx
        exact show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from ht.ge (mem_top _)))
    have hm := congrArg (Subgroup.map H.subtype) hh
    rw [subgroupOf_map_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,inf_comm] at hm
    exact hm
  obtain ⟨_,hnoncentral,_⟩ :=
    plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne
  exact ⟨heq, m_eq_yt_of_rigidity H M Mc (sourceResidual M Mc) (T : Subgroup G)
    (centralInvolutions T) (localModule T M) heq hint hMc (le_conjugateSpanBy _ _)
    (decomposition_of_intersectionCore_not_centralizing M Mc (localModule T M) T
      hM.1.2 ⟨e⟩ hnoncentral).le (sourceResidual_le _ _) hM.1.2⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
end
