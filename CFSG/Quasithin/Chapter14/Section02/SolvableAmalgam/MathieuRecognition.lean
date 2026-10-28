module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.CubicRecognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition
public import Theory.Mathieu.M12.SmallParabolicPair.RecognitionLocal
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The M₁₂ branch of source 14.2.22

An actual marked M₁₂ amalgam supplies the extraspecial first two-core,
its symmetric-three quotient and cubic fixed subgroup. The common marking
transports the second parabolic's elementary eight into the first core;
an element of the second parabolic then gives the required fusion of the
marked involution. Both quaternion subgroups are normal in its centralizer.

The normal-quaternion branch of I.4.6 therefore applies with its literal
centralizer and generalized Fitting subgroup. Ambient simplicity excludes
the normal elementary-eight alternative. The final source application keeps
the original local module and quotient action and yields the M₁₂ case of
Theorem E without an additional recognition or fusion premise.

Source: Aschbacher–Smith, 14.2.21–22 and I.4.6.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.GreenBook ChapterF.SourceAssembly ChapterF.SourceAssembly.Goldschmidt RankTwoAmalgam
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace MathieuRecognition

variable {G K : Type*} [Group G] [Group K]

private theorem map_centralizer (D : Subgroup G) (e : G ≃* K) :
    (centralizer (D : Set G)).map e.toMonoidHom =
      centralizer (D.map e.toMonoidHom : Set K) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩ v ⟨w,hw,rfl⟩
    change e w * e u = e u * e w
    simpa only [← map_mul] using congrArg e (hu w hw)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e y) ⟨y,hy,rfl⟩

private theorem fitting_eq (e : firstParabolic ≃* K) :
    generalizedFitting K = pCore 2 K := by
  rw [← map_generalizedFitting_equiv e, RecognitionLocal.fitting_eq_core, pCore_map_iso]

private def modelSylow (e : firstParabolic ≃* K) : Sylow 3 K :=
  RecognitionLocal.cubicSylow.mapSurjective (f := e.toMonoidHom)
    (by simpa only [MulEquiv.coe_toMonoidHom] using e.surjective)

private theorem fixed_eq (e : firstParabolic ≃* K) :
    pCore 2 K ⊓ centralizer
      (modelSylow e : Set K) =
        zpowers (e RecognitionLocal.point) := by
  have h := congrArg (fun D : Subgroup firstParabolic => D.map e.toMonoidHom)
    RecognitionLocal.cubic_fixed_core
  rw [map_inf _ _ _ e.injective,pCore_map_iso] at h
  change pCore 2 K ⊓ (centralizer
    ((RecognitionLocal.cubicSylow : Subgroup firstParabolic) : Set firstParabolic)).map
      e.toMonoidHom = _ at h
  rw [map_centralizer,MonoidHom.map_zpowers] at h
  exact h

private theorem quaternion_normal (e : firstParabolic ≃* K)
    (R : Subgroup (pCore 2 K)) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    (R.map (pCore 2 K).subtype).Normal := by
  let eQ := LocalCoreTransport.coreEquiv 2 e
  let S := R.map eQ.symm.toMonoidHom
  have hS : Nonempty (S ≃* QuaternionGroup 2) :=
    ⟨(eQ.symm.subgroupMap R).symm.trans hR.some⟩
  have hn := (RecognitionLocal.quaternion_normal_core S hS).map e.toMonoidHom e.surjective
  have he : (S.map (pCore 2 firstParabolic).subtype).map e.toMonoidHom =
      R.map (pCore 2 K).subtype := by
    change ((R.map eQ.symm.toMonoidHom).map _).map _ = _
    rw [map_map,map_map]
    congr 1
    ext x
    exact congrArg Subtype.val (eQ.apply_symm_apply x)
  exact he ▸ hn

private def hypotheses [Finite G] {v : G} (e : firstParabolic ≃* Extraspecial32.Centralizer v)
    (hp : e RecognitionLocal.point = Extraspecial32.distinguished v)
    (hfused : ∃ g : G, g * v * g⁻¹ ∈ Extraspecial32.coreInG v ∧ g * v * g⁻¹ ≠ v) :
    Extraspecial32.Hypotheses v := by
  have hF := fitting_eq e
  let eQ : Extraspecial32.Core v ≃* core :=
    (MulEquiv.subgroupCongr hF).trans
      ((LocalCoreTransport.coreEquiv 2 e).symm.trans firstCoreEquiv)
  refine ⟨?_, IsExtraspecial.of_mulEquiv eQ.symm extraspecial_core,
    (Nat.card_congr eQ.toEquiv).trans card_core, ?_,
    modelSylow e, ?_, hfused⟩
  · calc
      orderOf v = orderOf (Extraspecial32.distinguished v) :=
        (Subgroup.orderOf_coe (Extraspecial32.distinguished v))
      _ = orderOf RecognitionLocal.point := by rw [← hp]; exact e.orderOf_eq _
      _ = 2 := RecognitionLocal.point_order
  · refine ⟨(QuotientGroup.congr _ _ (MulEquiv.refl _) (by simpa using hF)).trans
      ((LocalCoreTransport.quotientEquiv 2 e).symm.trans firstCoreQuotient)⟩
  · change generalizedFitting (Extraspecial32.Centralizer v) ⊓
      centralizer (modelSylow e : Set (Extraspecial32.Centralizer v)) = _
    rw [hF, ← hp]
    exact fixed_eq e

private theorem quaternion_normal_fitting {v : G}
    (e : firstParabolic ≃* Extraspecial32.Centralizer v) :
    Extraspecial32.QuaternionSubgroupsNormal v := by
  change ∀ R : Subgroup (generalizedFitting (Extraspecial32.Centralizer v)),
    Nonempty (R ≃* QuaternionGroup 2) →
      (R.map (generalizedFitting (Extraspecial32.Centralizer v)).subtype).Normal
  rw [fitting_eq e]
  exact quaternion_normal e

/-- The marked point's centralizer is the actual first parabolic. -/
private theorem centralizer_point (T : Sylow 2 G) (H X : Subgroup G)
    (hHX : H ⊓ X = (T : Subgroup G))
    (hH : H = centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (e : firstParabolic ≃* H) :
    centralizer ({(e RecognitionLocal.point : G)} : Set G) = H := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  have hTH : (T : Subgroup G) ≤ H := hHX ▸ inf_le_left
  have hZH := hZT.trans hTH
  have hcenter : center H = zpowers (e RecognitionLocal.point) := by
    calc
      _ = (center firstParabolic).map e.toMonoidHom := by
        ext x
        constructor
        · intro hx
          exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩
        · rintro ⟨x,hx,rfl⟩
          exact (centerCongr e ⟨x,hx⟩).property
      _ = _ := by rw [RecognitionLocal.first_center,MonoidHom.map_zpowers]; rfl
  have hZgen : Z ≤ zpowers (e RecognitionLocal.point : G) := by
    intro a ha
    have hac : (⟨a,hZH ha⟩ : H) ∈ center H := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      exact (show (x : G) ∈ centralizer (Z : Set G) from hH ▸ x.property) a ha |>.symm
    rw [hcenter] at hac
    have hm := mem_map_of_mem H.subtype hac
    rw [MonoidHom.map_zpowers] at hm
    exact hm
  apply le_antisymm
  · apply le_trans ?_ (le_of_eq hH.symm)
    rw [show centralizer ({(e RecognitionLocal.point : G)} : Set G) =
      centralizer (zpowers (e RecognitionLocal.point : G) : Set G) from by
        rw [zpowers_eq_closure,centralizer_closure]]
    exact centralizer_le hZgen
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_center_iff.mp ((centerCongr e ⟨RecognitionLocal.point,
        RecognitionLocal.point_central⟩).property) ⟨x,hx⟩))

/-- The concrete second parabolic moves the marked point inside the first core. -/
private theorem fusion (H X : Subgroup G)
    (eH : firstParabolic ≃* H) (eX : secondParabolic ≃* X)
    (hc : ∀ t : sylowCandidate,
      (eH ⟨t,t.property.1⟩ : G) = (eX ⟨t,t.property.2⟩ : G)) :
    ∃ g : G, g * (eH RecognitionLocal.point : G) * g⁻¹ ∈ H.pCoreIn 2 ∧
      g * (eH RecognitionLocal.point : G) * g⁻¹ ≠ (eH RecognitionLocal.point : G) := by
  have hp := SmallLocal.Parabolics.m12_elementary_pair_transport H X eH eX hc
  dsimp only at hp
  obtain ⟨_,hEH,hEX,hn,_,_,hz,y,_,hy⟩ := hp
  have hzmark : (eH RecognitionLocal.point : G) =
      (eX ⟨z,elementary_le_secondParabolic (natural_le_elementary z_mem_natural)⟩ : G) :=
    hc ⟨z,core_le_sylowCandidate z_mem_core⟩
  rw [hzmark]
  refine ⟨y, hEH ?_, hy⟩
  exact hn.conj_mem ⟨_,hEX hz⟩ hz y

end MathieuRecognition

variable {G : Type*} [Group G] [Finite G]

/-- The original M₁₂ amalgam branch, with every local recognition premise derived. -/
theorem mathieu_twelve_recognition [IsSimpleGroup G]
    (T : Sylow 2 G) (H X : Subgroup G)
    (hHX : H ⊓ X = (T : Subgroup G))
    (_hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hH : H = centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hm : MathieuTwelve.IsM12Amalgam (inclusionAmalgam H X)) :
    Nonempty (G ≃* Sporadic.Mathieu.M12) := by
  obtain ⟨m⟩ := hm
  let f := (m.trans MathieuTwelve.concreteIso).symm
  have hc : ∀ t : sylowCandidate,
      (f.left ⟨t,t.property.1⟩ : G) = (f.right ⟨t,t.property.2⟩ : G) := by
    intro t
    exact (congrArg Subtype.val (f.left_commutes t)).trans
      (congrArg Subtype.val (f.right_commutes t)).symm
  let v : G := f.left RecognitionLocal.point
  have hC : Extraspecial32.Centralizer v = H :=
    MathieuRecognition.centralizer_point T H X hHX hH f.left
  let e : firstParabolic ≃* Extraspecial32.Centralizer v :=
    f.left.trans (MulEquiv.subgroupCongr hC.symm)
  have hp : e RecognitionLocal.point = Extraspecial32.distinguished v := Subtype.ext rfl
  have hfused : ∃ g : G, g * v * g⁻¹ ∈ Extraspecial32.coreInG v ∧ g * v * g⁻¹ ≠ v := by
    have hf := MathieuRecognition.fusion H X f.left f.right hc
    have hcore : Extraspecial32.coreInG v = H.pCoreIn 2 := by
      change (generalizedFitting (Extraspecial32.Centralizer v)).map
        (Extraspecial32.Centralizer v).subtype = _
      rw [MathieuRecognition.fitting_eq e,hC]
      rfl
    simpa only [hcore] using hf
  have h := MathieuRecognition.hypotheses e hp hfused
  rcases h.recognition_of_quaternion_normal (MathieuRecognition.quaternion_normal_fitting e) with hE | hm12
  · obtain ⟨E,hEn,_,hEcard,_⟩ := hE
    rcases hEn.eq_bot_or_eq_top with hbot | htop
    · simp [hbot] at hEcard
    · have hGcard : Nat.card G = 8 := by simpa [htop] using hEcard
      have hHcard : Nat.card H = 192 := (Nat.card_congr f.left.toEquiv).symm.trans card_firstParabolic
      have hle := Nat.card_le_card_of_injective H.subtype H.subtype_injective
      rw [hGcard,hHcard] at hle
      omega
  · exact hm12

/-- The literal source 14.2.22 M₁₂ branch of Theorem E. -/
theorem source_theoremE_of_mathieu_twelve_mark
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hcard : Nat.card (localModule T M) = 4) (hTM : (T : Subgroup G) ≤ M)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hHX : H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)) = (T : Subgroup G))
    (hH : H = centralizer (centralInvolutions T : Set G))
    (hm : MathieuTwelve.IsM12Amalgam
      (inclusionAmalgam H (sourceResidual M Mc ⊔ (T : Subgroup G)))) :
    ClassificationModels.IsTheoremEModel G := by
  let : IsSimpleGroup G := hG.simple
  exact .mathieu_twelve (mathieu_twelve_recognition T H _ hHX
    (plane_centralInvolutions_card T M hTM hcard e) hH hm)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
