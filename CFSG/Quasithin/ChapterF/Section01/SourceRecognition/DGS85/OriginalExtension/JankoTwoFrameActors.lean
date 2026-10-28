module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoEndpointGenerators

/-!
# Aligning the original Hall–Janko involution with one reduced frame

The frame's designated cubic agrees with the fixed-point-free cubic used in
the original normalizer construction. Its Cartan element is central in the
reduced second-core quotient. The original quotient and the faithful cubic
normalizer therefore lift inversion of that particular Cartan element.
Core preservation puts the same frame's z in the original core center, which
the same involution fixes. Both overlap squares of the reduced comparison
are retained throughout.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–230.
This establishes the simultaneous d-, z-, and k-actions. Compatible reduced
recognition remains an input; the quaternion word and the order-twelve
product are separate steps.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook GeneratorRelations
local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)

private theorem commuting_mem_normalizer_zpowers {A : Type*} [Group A]
    (a b : A) (hab : a*b=b*a) : b∈normalizer (zpowers a : Set A) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (b*a*b⁻¹)=zpowers a
  rw [←hab,mul_inv_cancel_right]

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem original_inverts_marked_cartan
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S)
    (k : parabolic L (reducedSylow L S) j) (hk : k^3=1)
    (hdk : reducedCubic j f*k=k*reducedCubic j f)
    (hkc : QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j)) k ∈
      center (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)))
    (x : parabolic L S j)
    (hx : (x:G)∉parabolic L (reducedSylow L S) j)
    (hdx : originalCubic h j f*x=x*originalCubic h j f) :
    x*inclusion (reduced_parabolic_le h j) k*x⁻¹=
      (inclusion (reduced_parabolic_le h j) k)⁻¹ := by
  let P := parabolic L S j
  let R := parabolic L (reducedSylow L S) j
  let a := inclusion (reduced_parabolic_le h j) k
  let q := QuotientGroup.mk' (pCore 2 P)
  let r := QuotientGroup.mk' (pCore 2 R)
  obtain ⟨d,c,hci,hd⟩ := original_second_quotient_marked_of_ne h i j e f hne
  let v := d.toMonoidHom.comp q
  let u := reducedSecondQuotientEquiv j f (r k)
  have hu : u ∈ center (S3 × C3) :=
    (Subgroup.centerCongr (reducedSecondQuotientEquiv j f) ⟨_,hkc⟩).property
  have hu1 : u.1=1 := by
    have hc : ∀ b : S3,b*u.1=u.1*b := by
      intro b
      exact congrArg Prod.fst (mem_center_iff.mp hu (b,1))
    exact (show ∀ a : S3,(∀ b : S3,b*a=a*b) → a=1 by decide +kernel) _ hc
  have hka : v a=(1,c u.2) := by
    have hh := hd (r k)
    have hm : coreQuotientMap h j (r k)=q a := coreQuotientMap_mk h j k
    rw [hm] at hh
    change v a=(u.1,c u.2) at hh
    rwa [hu1] at hh
  have hxodd : (v x).2∉alternatingGroup (Fin 3) :=
    fun he => hx ((original_second_quotient_reduced h j f d c hci hd x).mp he)
  have hk3 : a^3=1 := by
    simpa only [a,←map_pow,map_one] using
      congrArg (inclusion (reduced_parabolic_le h j)) hk
  have hc3 : (c u.2)^3=1 := by
    have hh := congrArg (fun y => (v y).2) hk3
    simpa [hka] using hh
  have hv : v (x*a*x⁻¹)=v a⁻¹ := by
    rw [map_mul,map_mul,map_inv,map_inv,hka]
    apply Prod.ext
    · simp
    · exact (show ∀ b a : S3,a^3=1 → b∉alternatingGroup (Fin 3) →
          b*a*b⁻¹=a⁻¹ by
        simp only [Equiv.Perm.mem_alternatingGroup]
        decide +kernel) _ _ hc3 hxodd
  have hda : originalCubic h j f*a=a*originalCubic h j f := by
    simpa only [originalCubic,map_mul] using congrArg (inclusion (reduced_parabolic_le h j)) hdk
  let aN : originalCubicNormalizer h j f := ⟨a,commuting_mem_normalizer_zpowers _ _ hda⟩
  let xN : originalCubicNormalizer h j f := ⟨x,commuting_mem_normalizer_zpowers _ _ hdx⟩
  have he : xN*aN*xN⁻¹=aN⁻¹ := by
    apply (originalCubicNormalizerEquiv h i j e f hne).injective
    apply d.injective
    exact hv
  exact congrArg Subtype.val he

private theorem reduced_frame_marked
    (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam) :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      F.d=reducedCubic j e.right ∧ F.k*F.z=F.z*F.k ∧
      QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))
        (inclusion (commonBorel_le_parabolic j) F.k) ∈
          center (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)) ∧
      F.QuaternionOrbit := by
  obtain ⟨F,hd,hz,hc,hF⟩ := model_frame_marked
  refine ⟨F.map e.symm,?_,?_,?_,F.quaternionOrbit_map e.symm hF⟩
  · rw [Frame.map_d]
    change e.right.symm F.d=reducedCubic j e.right
    rw [hd]
    rfl
  · rw [Frame.map_k,Frame.map_z]
    exact (map_mul e.middle.symm _ _).symm.trans
      ((congrArg e.middle.symm hz).trans (map_mul e.middle.symm _ _))
  · let v := LocalCoreTransport.quotientEquiv 2 e.right.symm
    have hh := (Subgroup.centerCongr v ⟨_,hc⟩).property
    change QuotientGroup.mk' _ (e.right.symm
      (HallJanko.j2Model.toMarking.amalgam.right F.k)) ∈ _ at hh
    change QuotientGroup.mk' _ (e.symm.right
      (HallJanko.j2Model.toMarking.amalgam.right F.k)) ∈ _ at hh
    rw [e.symm.right_commutes] at hh
    rw [Frame.map_k]
    exact hh

private theorem include_core_center {A : Type*} [Group A]
    (R P : Subgroup A) (hRP : R≤P) (he : twoCore R=twoCore P)
    (z : R) (hz : z∈pCore 2 R) (hzc : ∀ a∈pCore 2 R,z*a=a*z) :
    inclusion hRP z ∈ (center (pCore 2 P)).map (pCore 2 P).subtype := by
  let zP := inclusion hRP z
  have hzP : zP∈pCore 2 P := by
    apply (mem_map_iff_mem (f:=P.subtype) P.subtype_injective).mp
    change (z:A)∈twoCore P
    rw [←he]
    exact mem_map_of_mem R.subtype hz
  refine ⟨⟨zP,hzP⟩,mem_center_iff.mpr ?_,rfl⟩
  intro a
  have ha : (a:A)∈twoCore R := by
    rw [he]
    exact mem_map_of_mem P.subtype a.property
  obtain ⟨b,hb,hba⟩ := ha
  apply Subtype.ext
  apply Subtype.ext
  change (a:A)*(z:A)=(z:A)*(a:A)
  rw [←hba]
  exact congrArg Subtype.val (hzc b hb).symm

private theorem ambient_inversion {A : Type*} [Group A]
    (B R P : Subgroup A) (hBR : B≤R) (hRP : R≤P) (k : B) (x : P)
    (hi : x*inclusion hRP (inclusion hBR k)*x⁻¹=(inclusion hRP (inclusion hBR k))⁻¹) :
    (x:A)*(k:A)*(x:A)⁻¹=(k:A)⁻¹ := congrArg (fun y : P => (y:A)) hi

private theorem ambient_commuting {A : Type*} [Group A]
    (B R P : Subgroup A) (hBR : B≤R) (hRP : R≤P) (z : B) (x : P)
    (hc : x*inclusion hRP (inclusion hBR z)=inclusion hRP (inclusion hBR z)*x) :
    (x:A)*(z:A)=(z:A)*(x:A) := congrArg (fun y : P => (y:A)) hc

private theorem frame_original_inversion
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S≠reducedSylow L S)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (hd : F.d=reducedCubic j f)
    (hkc : QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))
      (inclusion (commonBorel_le_parabolic j) F.k)∈
        center (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)))
    (x : parabolic L S j) (hxR : (x:G)∉parabolic L (reducedSylow L S) j)
    (hdx : originalCubic h j f*x=x*originalCubic h j f) :
    (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ := by
  let kR := inclusion (commonBorel_le_parabolic j) F.k
  have hk3 : kR^3=1 := by
    have hh : F.k^3=1 := by rw [←F.k_order,pow_orderOf_eq_one]
    exact (map_pow _ F.k 3).symm.trans
      ((congrArg (inclusion (commonBorel_le_parabolic j)) hh).trans (map_one _))
  have hdk : reducedCubic j f*kR=kR*reducedCubic j f := by
    rw [←hd]
    exact F.d_commutes
  have hinv := original_inverts_marked_cartan h i j e f hne kR hk3 hdk hkc x hxR hdx
  exact ambient_inversion _ _ _ (commonBorel_le_parabolic j)
    (reduced_parabolic_le h j) F.k x hinv

private theorem frame_original_center_fixed
    (h : HypothesisF11 L S) (i j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (x : parabolic L S j) (hx : x^2=1)
    (hdx : originalCubic h j f*x=x*originalCubic h j f) :
    (x:G)*(F.z:G)=(F.z:G)*(x:G) := by
  let zR := inclusion (commonBorel_le_parabolic j) F.z
  let zP := inclusion (reduced_parabolic_le h j) zR
  have hzcenter := include_core_center _ _ (reduced_parabolic_le h j)
    (reduced_parabolic_core h j) zR F.z_core F.z_central
  exact ambient_commuting _ _ _ (commonBorel_le_parabolic j)
    (reduced_parabolic_le h j) F.z x
    (originalCubic_commuting_involution_fixes_core_center h j f x hx hdx zP hzcenter)

private theorem restrict_actor {A : Type*} [Group A]
    (B N P : Subgroup A) (k d z : A) (x : P)
    (hxB : (x:A)∈B) (hx : x^2=1) (hxN : (x:A)∉N)
    (hk : (x:A)*k*(x:A)⁻¹=k⁻¹)
    (hd : (x:A)*d=d*(x:A)) (hz : (x:A)*z=z*(x:A)) :
    ∃ y : B,y^2=1 ∧ (y:A)∉N ∧ (y:A)*k*(y:A)⁻¹=k⁻¹ ∧
      (y:A)*d=d*(y:A) ∧ (y:A)*z=z*(y:A) := by
  exact ⟨⟨x,hxB⟩,Subtype.ext (congrArg (fun y : P => (y:A)) hx),hxN,hk,hd,hz⟩

private theorem frame_cubic_commuting
    (h : HypothesisF11 L S) (i j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (hd : F.d=reducedCubic j f) (x : parabolic L S j)
    (hdx : originalCubic h j f*x=x*originalCubic h j f) :
    (x:G)*(F.d:G)=(F.d:G)*(x:G) := by
  have hh := congrArg (fun y : parabolic L S j => (y:G)) hdx
  change (reducedCubic j f:G)*(x:G)=(x:G)*(reducedCubic j f:G) at hh
  rw [←hd] at hh
  exact hh.symm

/-- A single source generator frame and an actual outer involution in the
full original Borel satisfy the d-, z-, and k-action relations simultaneously.
The involution lies in the full Borel outside the reduced Borel. -/
public theorem original_aligned_frame
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      ∃ x : commonBorel L S,
      F.d=reducedCubic j e.right ∧ F.k*F.z=F.z*F.k ∧ F.QuaternionOrbit ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧
      (x:G)*(F.z:G)=(F.z:G)*(x:G) := by
  obtain ⟨F,hd,hkz,hkc,hF⟩ := reduced_frame_marked i j e
  obtain ⟨k,x,_,_,hx,hxB,hxN,_,hdx,_,_⟩ :=
    exists_original_borel_outer_cubic_relations h i j e.left e.right hne
  have hxR : (x:G)∉parabolic L (reducedSylow L S) j := by
    intro hh
    apply hxN
    rw [←reduced_parabolic_inf_borel h j]
    exact ⟨hh,hxB⟩
  obtain ⟨y,hy,hyN,hyk,hyd,hyz⟩ := restrict_actor
    (commonBorel L S) (commonBorel L (reducedSylow L S)) (parabolic L S j)
    (F.k:G) (F.d:G) (F.z:G) x hxB hx hxN
    (frame_original_inversion h i j e.left e.right hne F hd hkc x hxR hdx)
    (frame_cubic_commuting h i j e.right F hd x hdx)
    (frame_original_center_fixed h i j e.right F x hx hdx)
  exact ⟨F,y,hd,hkz,hF,hy,hyN,hyk,hyd,hyz⟩

/-- Align the original involution with a specified marked frame. -/
public theorem original_actor_for_marked_frame
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (hd : F.d=reducedCubic j e.right)
    (hkc : QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))
      (inclusion (commonBorel_le_parabolic j) F.k) ∈
        center (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)))
 :
      ∃ x : commonBorel L S,
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧
      (x:G)*(F.z:G)=(F.z:G)*(x:G) := by
  obtain ⟨k,x,_,_,hx,hxB,hxN,_,hdx,_,_⟩ :=
    exists_original_borel_outer_cubic_relations h i j e.left e.right hne
  have hxR : (x:G)∉parabolic L (reducedSylow L S) j := by
    intro hh
    apply hxN
    rw [←reduced_parabolic_inf_borel h j]
    exact ⟨hh,hxB⟩
  obtain ⟨y,hy,hyN,hyk,hyd,hyz⟩ := restrict_actor
    (commonBorel L S) (commonBorel L (reducedSylow L S)) (parabolic L S j)
    (F.k:G) (F.d:G) (F.z:G) x hxB hx hxN
    (frame_original_inversion h i j e.left e.right hne F hd hkc x hxR hdx)
    (frame_cubic_commuting h i j e.right F hd x hdx)
    (frame_original_center_fixed h i j e.right F x hx hdx)
  exact ⟨y,hy,hyN,hyk,hyd,hyz⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
