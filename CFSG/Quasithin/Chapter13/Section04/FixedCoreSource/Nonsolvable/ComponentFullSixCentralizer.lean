module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSix
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationPoint
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryPermutation.SixCommutant
public import Theory.GroupTheory.SylowOuterCover
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# The full involution centralizer in the ordinary A₆ branch

The natural four-space and augmentation five-space both have trivial
invertible commutant. Transfer these calculations through the literal
component marking. Since the full moved orbit is now known to equal U,
the action of C_G(z) on U has normal A₆ image. Its scalar centralizer is
trivial, and the outer automorphism group is a two-group, so a Sylow
two-subgroup covers the remaining action.

An element centralizing U fixes the original central seed because
Z≤U⟨z⟩. The original fixed-generator centralizer and M=LT put it in
L₁T≤KT. Consequently C_G(z)=KT. The exact action kernel in K and the
Sylow supplement then make both full-orbit action kernels O₂(C_G(z)).
No full-orbit equality, scalar-action premise or centralizer conclusion
is assumed by the source applications.

Earlier M=LT, Chapter12/13.3 inputs and their producers remain explicit.
Final discharge belongs to qt-d-1341-fixed-core-source. The A₆/S₆ quotient
and outside-parabolic comparison, both-weight comparison, reciprocal
commutator exclusions and graph argument remain with this owner; earlier
LargeDistanceInput is still required for the separate linear-three row.
Source: Aschbacher–Smith A.1.41 and 13.4.10(7), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem commuting_of_coordinates
    {A U X : Type*} [Group A] [Group U] [AddCommGroup X] [Module (ZMod 2) X]
    (a : A →* MulAut U) (q : A →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (e : U ≃* Multiplicative X)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) X)
    (he : ∀ k v, (e (a k v)).toAdd = σ (q k) (e v).toAdd)
    (hscalar : ∀ f : X ≃ₗ[ZMod 2] X,
      (∀ k v, f (σ k v) = σ k (f v)) → f = LinearEquiv.refl _ _)
    (f : MulAut U) (hf : ∀ k v, f (a k v) = a k (f v)) : f = 1 := by
  let F := e.symm.trans (f.trans e)
  let c := AddEquiv.additiveMultiplicative (G := X)
  let b := c.symm.trans (F.toAdditive.trans c)
  let l : X ≃ₗ[ZMod 2] X := { b with map_smul' := ZMod.map_smul b }
  have hl (v : U) : l (e v).toAdd = (e (f v)).toAdd := by
    change (e (f (e.symm (e v)))).toAdd = _
    rw [e.symm_apply_apply]
  have heq : l = LinearEquiv.refl _ _ := hscalar l (by
    intro k v
    obtain ⟨k,rfl⟩ := hq k
    obtain ⟨w,hw⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv,←he,hl,hf,he,hl])
  apply MulEquiv.ext
  intro v
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [←hl,heq]
  rfl

private theorem six_natural_commuting_eq_refl
    (f : BinaryPermutation.natural (Fin 6) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 6))
    (hf : ∀ k v, f (BinaryPermutation.alternatingNaturalRepresentation (Fin 6) k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6) k (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨c,hc⟩ := BinaryAlternatingSix.Schur.natural_commuting_scalar f.toLinearMap hf
  simp only [LinearEquiv.coe_coe] at hc
  have hn : c ≠ 0 := by
    intro hz
    have hzero (v : BinaryPermutation.natural (Fin 6)) : v = 0 := by
      apply f.injective
      simpa only [hz,zero_smul,map_zero] using hc v
    have hr : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) = 0 := by
      let : Subsingleton (BinaryPermutation.natural (Fin 6)) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
      exact Module.finrank_zero_of_subsingleton
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hr
    norm_num at hr
  have hcone : c = 1 := (show c = 0 ∨ c = 1 from (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) c).resolve_left hn
  apply LinearEquiv.ext
  intro v
  simpa only [hcone,one_smul,LinearEquiv.refl_apply] using hc v

variable {T : Sylow 2 G} {K U : Subgroup G}
omit [Finite G] in
/-- Both actual ordinary A₆ module rows have trivial invertible commutant. -/
theorem ordinary_six_component_commuting_eq_one
    (DK : ChosenModule T K U) {z : G} (mark : ComponentModuleAt DK z)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (f : MulAut U)
    (hf : ∀ (k : K) (v : U),
      f (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v) =
        U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ (f v)) : f = 1 := by
  let a := U.normalizerMonoidHom.comp (inclusion DK.normalizes)
  cases mark with
  | linearThree q e he =>
    let ec := QuotientGroup.quotientMulEquivOfEq (Solvable.centralCore_eq_twoCore_of_ordinary eK)
    have hh := Nat.card_congr ((ec.symm.trans q).symm.trans eK).toEquiv
    rw [Matrix.PSL3Two.card_SL,nat_card_alternatingGroup] at hh
    norm_num at hh
  | naturalSix q e he =>
    exact commuting_of_coordinates a (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) he
      six_natural_commuting_eq_refl f hf
  | coreSix m _ =>
    exact commuting_of_coordinates a (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
      (m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)) m.coordinate
      (BinaryPermutation.alternatingCoreRepresentation (Fin 6)) m.equivariant
      BinaryPermutation.SixCommutant.commuting_eq_refl f hf

private theorem six_module_sylow_supplement
    (S : Sylow 2 G) (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsElementaryAbelian 2 U] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hred : IsPReduced 2 U) (hm : ⁅U,K⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hscalar : ∀ f : MulAut U,
      (∀ (k : K) (v : U), f (MulAut.conjNormal k.val v) =
        MulAut.conjNormal k.val (f v)) → f = 1) :
    (K ⊔ (S : Subgroup G)) ⊔ centralizer (U : Set G) = ⊤ := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  let B := K.map q
  let a := NormalElementaryQuotient.conjugationAut U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have ha (k : G) : a (q k) = MulAut.conjNormal k := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact NormalElementaryQuotient.conjugationAut_apply U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) k v
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : eK x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
      ((centerCongr eK) ⟨x,hx⟩).property
    exact eK.injective (hh.trans eK.map_one.symm)
  let eB := (reducedQuasisimpleImageEquiv U K hred hz hm).symm.trans eK
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective C)
  have hc : centralizer (B : Set (G ⧸ C)) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have he : a x = 1 := hscalar (a x) (by
      intro k v
      rw [←ha]
      change (a x * a (q k.val)) v = (a (q k.val) * a x) v
      rw [←map_mul,←map_mul,(hx (q k.val) (mem_map_of_mem q k.property)).symm])
    apply NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    apply LinearMap.ext
    intro v
    change Additive.ofMul (a x v.toMul) = _
    rw [he,map_one]
    rfl
  have hout : IsPGroup 2 (MulAut.Outer B) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr (MulAut.outerCongr eB).toEquiv,AlternatingSix.ShadowLocal.outer_card]
    decide
  have hs := sup_centralizer_sup_sylow_eq_top B hout
    (S.mapSurjective (QuotientGroup.mk'_surjective C))
  rw [hc,sup_bot_eq] at hs
  have hh := congrArg (comap q) hs
  change (K.map q ⊔ (S : Subgroup G).map q).comap q = _ at hh
  rw [←Subgroup.map_sup,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
  exact hh

variable {L V : Subgroup G}

/-- Original 13.4.10(7) for the ordinary A₆ component, with no orbit-equality premise. -/
theorem ordinary_six_full_centralizer
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    H = K ⊔ (T : Subgroup G) ∧
      ⁅conjugateSpanBy Z H,K⁆ = ⁅conjugateSpanBy Z K,K⁆ ∧
      conjugateSpanBy Z H = conjugateSpanBy Z K ∧
      H ≤ normalizer ((⁅conjugateSpanBy Z K,K⁆ : Subgroup G) : Set G) := by
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let X := K ⊔ (T : Subgroup G)
  have hKz := hK.1
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  have hTK := hTH.trans hHN
  obtain ⟨DK,⟨mark⟩,_,⟨eL⟩,hLK,_,_,_,_,_⟩ := ordinary_six_component_geometry
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨hQ,hW,hn⟩ := ordinary_six_full_orbit_eq
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  have hUH : U ≤ H := DK.le_sylow.trans hTH
  let A := K.subgroupOf H
  let B := U.subgroupOf H
  let S := T.subtype hTH
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 B := by
    let := DK.elementary
    exact IsElementaryAbelian.subgroupOf hUH
  let a := subgroupOfEquivOfLe hKz
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := subgroupOfEquivOfLe hUH
  let := component_quotient_quasisimple h1332 hfK
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hr : IsPReduced 2 B := by
    have hh := (component_full_orbit h₀ h structural D m hindex z hzT hzL hKz hHN hKM).2.1
    rwa [hQ] at hh
  have hmove : ⁅B,A⁆ = B := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hKz]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hne : ⁅B,A⁆ ≠ ⊥ := by
    rw [hmove]
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact DK.ne_bot hh
  have hscalar (f : MulAut B) (hf : ∀ (k : A) (v : B),
      f (MulAut.conjNormal k.val v) = MulAut.conjNormal k.val (f v)) : f = 1 := by
    let F : MulAut U := b.symm.trans (f.trans b)
    have hF : F = 1 := ordinary_six_component_commuting_eq_one DK mark eK F (by
      intro k v
      apply b.symm.injective
      change f (MulAut.conjNormal (⟨k.val,hKz k.property⟩ : H) (b.symm v)) =
        MulAut.conjNormal (⟨k.val,hKz k.property⟩ : H) (f (b.symm v))
      exact hf ⟨⟨k.val,hKz k.property⟩,k.property⟩ (b.symm v))
    apply MulEquiv.ext
    intro v
    apply b.injective
    have hh := congrArg (fun t : MulAut U => t (b v)) hF
    simpa only [F,MulEquiv.trans_apply,b.symm_apply_apply,MulAut.one_apply] using hh
  have hsupp := six_module_sylow_supplement S A B hr hne (aq.trans eK) hscalar
  have hseed := component_seed_split h₀ hzT hz1 hKz hTK
  rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hKz hKM] at hseed
  have hZU : Z ≤ U ⊔ zpowers z.val := hseed ▸ le_conjugateSpanBy Z K
  have hC : (centralizer (B : Set H)).map H.subtype ≤ X := by
    rintro x ⟨x,hx,rfl⟩
    have hxU : x.val ∈ centralizer (U : Set G) := fun v hv =>
      congrArg Subtype.val (hx ⟨v,hUH hv⟩ hv)
    have hxz : x.val ∈ centralizer (zpowers z.val : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact x.property
    have hZc : U ⊔ zpowers z.val ≤ centralizer ({x.val} : Set G) :=
      sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hxU v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (hxz v hv))
    have hZx : x.val ∈ centralizer (Z : Set G) :=
      fun v hv => mem_centralizer_singleton_iff.mp (hZc (hZU hv))
    have hMx : x.val ∈ normalizer (L : Set G) := by
      rw [←fixed_generator_centralizer h structural D m
        ⟨m.constant.property,m.constant_fixed⟩
        (fun hh => m.constant_ne_one (Subtype.ext hh))]
      exact mem_centralizer_singleton_iff.mpr
        (hZx m.constant.val (m.constant_mem_central_four h structural).2).symm
    have hp : x.val ∈ Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
      rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
      exact ⟨hM ▸ hMx,x.property⟩
    exact sup_le_sup_right hLK _ hp
  have hH : H = X := by
    apply le_antisymm ?_ (sup_le hKz hTH)
    have hh := congrArg (map H.subtype) hsupp
    change ((A ⊔ (T : Subgroup G).subgroupOf H) ⊔ centralizer (B : Set H)).map H.subtype =
      (⊤ : Subgroup H).map H.subtype at hh
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hKz,
      map_subgroupOf_eq_of_le hTH,←MonoidHom.range_eq_map,range_subtype] at hh
    change H ≤ X
    rw [←hh]
    exact sup_le le_rfl hC
  exact ⟨hH,hQ,hW,hn⟩


/-- Both literal full-centralizer actions have precisely O₂(C_G(z)) as kernel. -/
theorem ordinary_six_full_action_kernels
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    H ⊓ centralizer ((⁅conjugateSpanBy Z K,K⁆ : Subgroup G) : Set G) = H.pCoreIn 2 ∧
      H ⊓ centralizer (conjugateSpanBy Z H : Set G) = H.pCoreIn 2 := by
  have hKz := hK.1
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  obtain ⟨hH,hQ,hW,hn⟩ := ordinary_six_full_centralizer
    h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK eK
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let A := K.subgroupOf H
  let B := U.subgroupOf H
  have hUH : U ≤ H := by
    obtain ⟨_,_,_,_,_,_,_,hq,_,_⟩ := component_full_orbit h₀ h structural D m hindex z hzT hzL hKz hHN hKM
    rw [hQ] at hq
    exact hq.trans (Solvable.centralizerOmegaOrbit_le hzT)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hr : IsPReduced 2 B := by
    have hh := (component_full_orbit h₀ h structural D m hindex z hzT hzL hKz hHN hKM).2.1
    rwa [hQ] at hh
  let : IsElementaryAbelian 2 B := hr.elementary
  let a := subgroupOfEquivOfLe hKz
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let eA := aq.trans eK
  let := component_quotient_quasisimple h1332 hfK
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : eA x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
      ((centerCongr eA) ⟨x,hx⟩).property
    exact eA.injective (hh.trans eA.map_one.symm)
  have hmove : ⁅B,A⁆ = B := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hKz]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz (hTH.trans hHN)
  have hne : ⁅B,A⁆ ≠ ⊥ := by
    rw [hmove]
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact component_moved_ne_bot h structural m hKM hh
  let C := centralizer (B : Set H)
  let q := QuotientGroup.mk' C
  have hquot : IsPGroup 2 (H ⧸ A) := by
    apply isPGroup_quotient_of_sup_eq_top A ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup hKz hTH,←hH,subgroupOf_self]
  have hp : IsPGroup 2 C := by
    have hh := MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient q A hquot
      (Nat.card_congr (reducedQuasisimpleImageEquiv B A hr hz hne).symm.toEquiv)
    rwa [QuotientGroup.ker_mk'] at hh
  have hC : C = pCore 2 H := le_antisymm
    (le_sSup ⟨inferInstance,hp⟩) (le_centralizer_iff.mp hr.le_centralizer_pCore)
  have hm : C.map H.subtype = H ⊓ centralizer (U : Set G) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,fun v hv => congrArg Subtype.val (hx ⟨v,hUH hv⟩ hv)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,(fun v hv => Subtype.ext (hc v.val hv)),rfl⟩
  have hk : H ⊓ centralizer (U : Set G) = H.pCoreIn 2 := by
    rw [←hm,hC]
    rfl
  have hfull := (component_full_orbit h₀ h structural D m hindex z hzT hzL hKz hHN hKM).2.2.2.2.2.2.2.2.2
  rw [hQ] at hfull
  exact ⟨hk,hfull.trans hk⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
