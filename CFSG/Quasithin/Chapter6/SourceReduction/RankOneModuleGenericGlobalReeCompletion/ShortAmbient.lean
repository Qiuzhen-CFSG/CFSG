module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortCentralizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient.Counting
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Action
public import Theory.SpecificGroups.ReeF4.SourceCompletion.RootClasses
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient.Plane

/-!
# The entire ambient short centralizer in the original Ree row

Choose a conjugate inside the full original left normalizer whose centralizer
in T is Sylow locally. The full endpoint marking identifies the entire model
centralizer. One-way ambient-to-extension involution fusion bounds every
ambient centralizer two-subgroup by that local Sylow, proving extremality.
Native exhaustion preserves the short class under the full endpoint action.

The new marker retains O₂(L), the linear radical, the same literal extension
map, and the original nonfusion invariant. The extension Sylow is precisely
the original T marked by the full middle map; both centralizer Sylows are
proved simultaneously. Only earlier native exhaustion and endpoint fusion
are explicit. This is the F.4.40 selection used in F.4.42, printed pp.294–295
(`refs/quasithin.pdf`). The whole long-centralizer comparison now supplies
the commuting-class incidence count and unique fixed cosets. The same
chosen marker has a faithful native PSL₂ action on its literal root plane.
Full endpoint invariance transports the nontrivial elementary plane to the
actual local centralizer. I.8.5 makes a proper local subgroup act solvably,
contradicting the faithful PSL₂ action. Thus the entire ambient centralizer
lies in the original left normalizer, and its equivalence with the extension
centralizer is the restriction of the same literal endpoint map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G]

private theorem centralizer_subgroupOf (P : Subgroup G) (v : P) :
    centralizer ({v} : Set P) = (centralizer ({v.val} : Set G)).subgroupOf P := by
  ext x
  change (x ∈ centralizer ({v} : Set P)) ↔ x.val ∈ centralizer ({v.val} : Set G)
  rw [mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

/-- The left endpoint and the full overlap mark the same original subgroup. -/
theorem ReeNormalizerMarking.left_sylow_eq_middle
    {L K U S : Subgroup G} {m : ℕ} (D : ReeNormalizerMarking L K S m)
    (hUI : U ≤ normalizer (L : Set G) ⊓ normalizer (K : Set G)) :
    (U.subgroupOf (normalizer (L : Set G))).map D.leftToCarrier =
      (U.subgroupOf (normalizer (L : Set G) ⊓ normalizer (K : Set G))).map D.middleToCarrier := by
  have hc (x : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
      D.leftToCarrier (inclusion inf_le_left x) = D.middleToCarrier x := by
    apply Subtype.ext
    change (D.full.left ⟨x.val,x.property.1⟩).val = (D.full.middle x).val
    exact congrArg (fun y : D.extension.left => y.val) (D.full.left_commutes x)
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x.val,hUI hx⟩,hx,(hc ⟨x.val,hUI hx⟩).symm⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨inclusion inf_le_left x,hx,hc x⟩

private theorem sylow_centralizer_map
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    (f : P →* E) (hf : Function.Injective f) (v : P) (U : Subgroup P)
    (hC : (centralizer ({v} : Set P)).map f = centralizer ({f v} : Set E))
    (hR : ∃ R : Sylow 2 (centralizer ({v} : Set P)),
      (R : Subgroup (centralizer ({v} : Set P))) = U.subgroupOf (centralizer ({v} : Set P))) :
    ∃ R : Sylow 2 (centralizer ({f v} : Set E)),
      (R : Subgroup (centralizer ({f v} : Set E))) =
        (U.map f).subgroupOf (centralizer ({f v} : Set E)) := by
  let e : centralizer ({v} : Set P) ≃* centralizer ({f v} : Set E) :=
    ((centralizer ({v} : Set P)).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hC)
  obtain ⟨R,hR⟩ := hR
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (R : Subgroup (centralizer ({v} : Set P))).map e.toMonoidHom = _
  rw [hR]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,rfl⟩
  · rintro ⟨x,hx,he⟩
    have hxC : x ∈ centralizer ({v} : Set P) := by
      apply mem_centralizer_singleton_iff.mpr
      apply hf
      change f x = y.val at he
      rw [map_mul,map_mul,he]
      exact mem_centralizer_singleton_iff.mp y.property
    exact ⟨⟨x,hxC⟩,hx,Subtype.ext he⟩

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The short marker may be chosen extremal in the original T, retaining the
same full-normalizer extension and literal centralizer map. -/
theorem Preparation.ree_short_extremal_comparison
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hfusion : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (D.leftToCarrier x) (D.leftToCarrier y)) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      (∃ R : Sylow 2 (centralizer ({v} : Set (normalizer (L : Set G)))),
        (R : Subgroup (centralizer ({v} : Set (normalizer (L : Set G))))) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).subgroupOf
            (centralizer ({v} : Set (normalizer (L : Set G))))) ∧
      (∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
        (R : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier ∧
        D.extension.baseHom t ∈ S ∧
        ∃ R : Sylow 2 (centralizer ({D.extension.baseHom t} : Set D.extension.carrier)),
          (R : Subgroup (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) =
            (S : Subgroup D.extension.carrier).subgroupOf
              (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  obtain ⟨_,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL] using
      pCoreIn_le_sylow L (T.subtype hTL)
  obtain ⟨t,v,ht,_,hvQ,hv2,hmark,hmap,_,h3,hnf⟩ :=
    d.ree_short_centralizer_comparison h hH hp m he D
  have hc : (centralizer ({v} : Set (normalizer (L : Set G)))).map D.leftToCarrier =
      centralizer ({D.leftToCarrier v} : Set D.extension.carrier) := by
    rw [centralizer_subgroupOf,hmap,hmark]
  obtain ⟨g,w,hgw,hwT,hw2,hwmap,hwlocal,hwsylow⟩ :=
    ReeF4.SourceCompletion.ShortCentralizerGeometry.exists_extremal_endpoint_conjugate
      T (normalizer (L : Set G)) h.sylow_normalizes D.leftToCarrier
      D.leftToCarrier_injective v (hQT hvQ) hv2 hfusion hc
  let t' := (D.leftToCarrier g).val t
  have hgE : D.leftToCarrier g ∈ D.extension.left.subgroupOf D.extension.carrier := by
    rw [←D.leftToCarrier_range]
    exact ⟨g,rfl⟩
  have hCt : centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ≤
      D.extension.left.subgroupOf D.extension.carrier := by
    rw [←hmap,←D.leftToCarrier_range]
    exact Subgroup.map_le_range _ _
  obtain ⟨ht',htQ',_⟩ := GeneralReeFour.ShortAmbient.extension_short_conjugate
    D.extension hm hexhaust ht hCt (D.leftToCarrier g) hgE
  have hmark' : D.leftToCarrier w = D.extension.baseHom t' := by
    rw [←hgw,map_mul,map_mul,map_inv,hmark]
    exact (GeneralReeFour.ShortAmbient.baseHom_conjugation D.extension
      (D.leftToCarrier g) t).symm
  have hgwG : g.val * v.val * g.val⁻¹ = w.val := congrArg Subtype.val hgw
  have hwQ : w.val ∈ L.pCoreIn 2 := by
    rw [←hgwG]
    exact (mem_normalizer_iff.mp
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L) g.property) v.val).mp hvQ
  have h3w : 3 ∣ Nat.card (solvableResidual (centralizer ({w.val} : Set G))) := by
    have hh := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g.val) v.val).solvableResidualEquiv.toEquiv
    change Nat.card (solvableResidual (centralizer ({v.val} : Set G))) =
      Nat.card (solvableResidual (centralizer ({g.val * v.val * g.val⁻¹} : Set G))) at hh
    rw [hgwG] at hh
    exact hh ▸ h3
  have hTI : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    le_inf h.sylow_normalizes (hTK.trans (residual H).le_normalizer)
  obtain ⟨S,hS⟩ := GeneralReeFour.extension_middle_sylow D.extension hm D.full.middle (T.subtype hTI)
  have hleftS : ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).map D.leftToCarrier =
      (S : Subgroup D.extension.carrier) := (D.left_sylow_eq_middle hTI).trans hS.symm
  have hext := sylow_centralizer_map D.leftToCarrier D.leftToCarrier_injective w
    ((T : Subgroup G).subgroupOf (normalizer (L : Set G))) hwmap hwlocal
  rw [hleftS,hmark'] at hext
  have hwtS : D.extension.baseHom t' ∈ S := by
    change D.extension.baseHom t' ∈ (S : Subgroup D.extension.carrier)
    rw [←hmark',←hleftS]
    exact mem_map_of_mem D.leftToCarrier hwT
  refine ⟨t',w,ht',htQ',hwQ,hwT,hw2,hmark',?_,hwlocal,hwsylow,
    ⟨S,hS,hwtS,hext⟩,h3w,?_⟩
  · rw [←centralizer_subgroupOf,hwmap,hmark']
  · intro z hz hz2 hzw
    exact hnf z hz hz2 (hzw.trans (isConj_iff.mpr ⟨g.val,hgwG⟩).symm)

/-- The full long-centralizer comparison and cross-endpoint fusion give
unique fixed cosets in the actual ambient short centralizer. -/
theorem Preparation.ree_short_unique_fixed_cosets
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (v : normalizer (L : Set G)) (hv2 : orderOf v.val = 2)
    (hmap : ((centralizer ({v.val} : Set G)).subgroupOf
        (normalizer (L : Set G))).map D.leftToCarrier =
      centralizer ({D.leftToCarrier v} : Set D.extension.carrier))
    (hSylow : ∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
      (R : Subgroup (centralizer ({v.val} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G)))
    (hfusion : ∀ x : normalizer (L : Set G),
      ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.rightToCarrier y)))
    (z : center (residual H)) (hz2 : orderOf z = 2) :
    ∀ a : centralizer ({v.val} : Set G), IsConj z.val.val a.val →
      ∃! q : centralizer ({v.val} : Set G) ⧸
        (normalizer (L : Set G)).subgroupOf (centralizer ({v.val} : Set G)), a • q = q := by
  let zN : normalizer (residual H : Set G) :=
    ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
  have hzG : orderOf z.val.val = 2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hz2]
  have hC := d.ree_central_involution_centralizers h hH hp m he 1 z.val.val
    (mem_map_of_mem _ z.property) hzG
  have hZ := (d.ree_long_centralizer_comparison h hH hp m he D z hz2).1
  apply GeneralReeFour.ShortAmbient.unique_fixed_of_endpoint_fusion
    (normalizer (L : Set G)) (normalizer (residual H : Set G))
    D.leftToCarrier D.rightToCarrier D.leftToCarrier_injective D.rightToCarrier_injective
    v zN hv2 hzG hC hZ hmap hfusion
  obtain ⟨R,hR⟩ := hSylow
  exact ⟨R,hR ▸ subgroupOf_mono _ h.sylow_normalizes⟩

/-- On the same extremal marker, the ambient unique-fixed-coset comparison
and a faithful literal native PSL₂ action are simultaneously available.
Only earlier native exhaustion and endpoint fusion are assumed. -/
theorem Preparation.ree_short_incidence_action
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hleft : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (D.leftToCarrier x) (D.leftToCarrier y))
    (hcross : ∀ x : normalizer (L : Set G),
      ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.rightToCarrier y))) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      (∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
        (R : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier ∧
        D.extension.baseHom t ∈ S ∧
        ∃ R : Sylow 2 (centralizer ({D.extension.baseHom t} : Set D.extension.carrier)),
          (R : Subgroup (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) =
            (S : Subgroup D.extension.carrier).subgroupOf
              (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) ∧
      (∀ z : center (residual H), orderOf z = 2 →
        ∀ a : centralizer ({v.val} : Set G), IsConj z.val.val a.val →
          ∃! q : centralizer ({v.val} : Set G) ⧸
            (normalizer (L : Set G)).subgroupOf (centralizer ({v.val} : Set G)), a • q = q) ∧
      (ReeF4.ElementaryTwoBound.Replacement.V m ≤ centralizer ({t} : Set (Model m))) ∧
      ∃ f : LargeLocalSeeds.LinearQuotient m →* centralizer ({t} : Set (Model m)),
        ∃ ρ : LargeLocalSeeds.LinearQuotient m →*
            MulAut (ReeF4.ElementaryTwoBound.Replacement.V m),
          Function.Injective f ∧ Function.Injective ρ ∧
          ∀ x w, (ρ x w : Model m) = (f x).val * w.val * (f x).val⁻¹ := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  obtain ⟨t,v,ht,htR,hvQ,hvT,hv2,hmark,hmap,_,hSylow,hExt,_,_⟩ :=
    d.ree_short_extremal_comparison h hH hp m he D hexhaust hleft
  have hmap' : ((centralizer ({v.val} : Set G)).subgroupOf
      (normalizer (L : Set G))).map D.leftToCarrier =
      centralizer ({D.leftToCarrier v} : Set D.extension.carrier) := by
    rw [hmark,hmap]
  have hCn : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear := by
    intro x hx
    apply (D.extension.baseHom_mem_family_iff (ReeF4.SmallCompletion.conj_injective m hm) false x).mp
    have he : D.extension.baseHom x ∈ centralizer ({D.extension.baseHom t} : Set D.extension.carrier) :=
      mem_centralizer_singleton_iff.mpr
        ((show Commute x t from mem_centralizer_singleton_iff.mp hx).map D.extension.baseHom).eq
    rw [←hmap] at he
    change D.extension.baseHom x ∈ D.extension.left.subgroupOf D.extension.carrier
    rw [←D.leftToCarrier_range]
    exact map_le_range _ _ he
  obtain ⟨f,hf,hfa⟩ := ReeF4.SourceCompletion.ShortCentralizerGeometry.short_plane_faithful_psl hm ht hCn
  refine ⟨t,v,ht,htR,hvQ,hvT,hv2,hmark,hmap,hSylow,hExt,?_,
    ReeF4.SourceCompletion.ShortCentralizerGeometry.plane_le_short_centralizer htR,
    f,(ReeF4.SourceCompletion.ShortCentralizerGeometry.shortPlaneAction hm hCn).comp f,hf,hfa,?_⟩
  · exact d.ree_short_unique_fixed_cosets h hH hp m he D v hv2 hmap' hSylow hcross
  · intro x w
    exact ReeF4.SourceCompletion.ShortCentralizerGeometry.shortPlaneAction_apply hm hCn (f x) w

omit he in
private theorem right_center_native_marking
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (z : center (residual H)) (hz2 : orderOf z = 2) :
    ∃ ze : Model m, IsLongRootInvolution ze ∧
      D.rightToCarrier ⟨z.val.val,(residual H).le_normalizer z.val.property⟩ =
        D.extension.baseHom ze := by
  have hm := d.ree_parameter_positive h hp m 1 .suzuki D.pure.right
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  let a : P := ⟨z.val.val,hKP z.val.property⟩
  let f := (parabolic m .suzuki).subtype.comp D.pure.right.toMonoidHom
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hH.1.1.2 hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hR : ((residual H).subgroupOf P).map f = localFactor m .suzuki := by
    rw [hres,show f = (parabolic m .suzuki).subtype.comp D.pure.right.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq _ D.pure.right.surjective]
    exact parabolic_solvableResidual_map hm .suzuki
  have haR : f a ∈ localFactor m .suzuki := hR ▸ mem_map_of_mem f z.val.property
  have hZ : f a ∈ (center (localFactor m .suzuki)).map (localFactor m .suzuki).subtype := by
    refine ⟨⟨f a,haR⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    obtain ⟨b,hb,hbr⟩ := (hR.symm ▸ r.property : r.val ∈ ((residual H).subgroupOf P).map f)
    apply Subtype.ext
    change r.val * f a = f a * r.val
    rw [←hbr,←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    exact congrArg (fun k : residual H => k.val) (mem_center_iff.mp z.property ⟨b.val,hb⟩)
  rw [ReeF4.SourceCompletion.suzuki_center_eq_longRoot hm] at hZ
  have hf : Function.Injective f := (parabolic m .suzuki).subtype_injective.comp D.pure.right.injective
  have ha2 : orderOf (f a) = 2 := by
    rw [orderOf_injective f hf,←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe z.val).trans ((Subgroup.orderOf_coe z).trans hz2)
  obtain ⟨c,hc⟩ := (mem_longRootGroup m (f a)).mp hZ
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [←hc,hc0,longRootElement_zero,orderOf_one] at ha2
    omega
  refine ⟨f a,⟨c,hc0,hc ▸ IsConj.refl _⟩,?_⟩
  apply Subtype.ext
  exact D.right_marking a

/-- F.4.42 containment for any selected extremal short marker in the same
full-normalizer extension. Only the earlier cross-endpoint fusion remains
as a mathematical premise; the plane, faithful action and I.8.5 premises
are proved and applied here. -/
theorem Preparation.ree_short_centralizer_le_normalizer
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (t : Model m) (v : normalizer (L : Set G))
    (ht : IsShortRootInvolution t) (htR : t ∈ radical m .linear)
    (hv2 : orderOf v.val = 2) (hmark : D.leftToCarrier v = D.extension.baseHom t)
    (hmap : ((centralizer ({v.val} : Set G)).subgroupOf
        (normalizer (L : Set G))).map D.leftToCarrier =
      centralizer ({D.extension.baseHom t} : Set D.extension.carrier))
    (hSylow : ∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
      (R : Subgroup (centralizer ({v.val} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G)))
    (hcross : ∀ x : normalizer (L : Set G), ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.rightToCarrier y))) :
    centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  let P := normalizer (L : Set G)
  let M := centralizer ({v.val} : Set G)
  let X := P.subgroupOf M
  let swap : X ≃* M.subgroupOf P := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let e := swap.trans (((M.subgroupOf P).equivMapOfInjective D.leftToCarrier
    D.leftToCarrier_injective).trans (MulEquiv.subgroupCongr hmap))
  have heval (a : X) : (e a).val = D.leftToCarrier ⟨a.val.val,a.property⟩ := rfl
  have hC : centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ≤
      D.extension.left.subgroupOf D.extension.carrier := by
    rw [←hmap,←D.leftToCarrier_range]
    exact map_le_range _ _
  have hX : X = ⊤ := by
    apply GeneralReeFour.ShortAmbient.eq_top_of_extension_plane D.extension hm ht htR hC X e
    rintro a ⟨w,hw,haw⟩
    obtain ⟨z,hz,hz2,_⟩ := d.ree_right_center_involution h hH hp m he
    obtain ⟨z,hz,rfl⟩ := hz
    let zC : center (residual H) := ⟨z,hz⟩
    have hzC2 : orderOf zC = 2 := by
      rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
      exact hz2
    obtain ⟨ze,hze,hzemark⟩ := right_center_native_marking d h hH hp m D zC hzC2
    have hw1 : w.val ≠ 1 := fun hh => hw (Subtype.ext hh)
    have hwlong := ReeF4.SourceCompletion.ShortCentralizerGeometry.plane_nonidentity_long m w.property hw1
    have hw2 := orderOf_of_isLongRootInvolution hwlong
    let x : P := ⟨a.val.val,a.property⟩
    have hxmark : D.leftToCarrier x = D.extension.baseHom w.val := (heval a).symm.trans haw
    have hx2 : orderOf x.val = 2 := by
      rw [Subgroup.orderOf_coe,←orderOf_injective D.leftToCarrier D.leftToCarrier_injective,
        hxmark,orderOf_injective D.extension.baseHom
          (D.extension.baseHom_injective (ReeF4.SmallCompletion.conj_injective m hm))]
      exact hw2
    have hconj := D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.long_class_isConj hze hwlong)
    have hg : IsConj zC.val.val a.val.val := by
      have hh := (hcross x ⟨zC.val.val,(residual H).le_normalizer zC.val.property⟩ hx2 hz2).mpr
        (by rw [hxmark,hzemark]; exact hconj.symm)
      exact hh.symm
    have hmap' : (M.subgroupOf P).map D.leftToCarrier =
        centralizer ({D.leftToCarrier v} : Set D.extension.carrier) := by rw [hmark]; exact hmap
    exact d.ree_short_unique_fixed_cosets h hH hp m he D v hv2 hmap' hSylow hcross zC hzC2 a.val hg
  intro a ha
  have hh : (⟨a,ha⟩ : M) ∈ X := by rw [hX]; trivial
  exact hh

/-- The full general Ree F.4.42 family on the original ambient row. The
chosen marker is extremal in both the original Sylow and the same marked
extension, and the entire ambient centralizer comparison is the restriction
of the supplied full left-endpoint map. Native exhaustion and earlier
endpoint fusion are the only additional source premises. -/
theorem Preparation.ree_short_ambient_comparison
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hleft : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (D.leftToCarrier x) (D.leftToCarrier y))
    (hcross : ∀ x : normalizer (L : Set G),
      ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.rightToCarrier y))) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      (∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
        (R : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier ∧
        D.extension.baseHom t ∈ S ∧
        ∃ R : Sylow 2 (centralizer ({D.extension.baseHom t} : Set D.extension.carrier)),
          (R : Subgroup (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) =
            (S : Subgroup D.extension.carrier).subgroupOf
              (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val) ∧
      ∃ hC : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G),
        ∃ e : centralizer ({v.val} : Set G) ≃*
            centralizer ({D.extension.baseHom t} : Set D.extension.carrier),
          ∀ x, (e x).val = D.leftToCarrier ⟨x.val,hC x.property⟩ := by
  obtain ⟨t,v,ht,htR,hvQ,hvT,hv2,hmark,hmap,_,hSylow,hExt,h3,hnf⟩ :=
    d.ree_short_extremal_comparison h hH hp m he D hexhaust hleft
  have hC := d.ree_short_centralizer_le_normalizer h hH hp m he D t v ht htR
    hv2 hmark hmap hSylow hcross
  let e := (subgroupOfEquivOfLe hC).symm.trans
    ((((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).equivMapOfInjective
      D.leftToCarrier D.leftToCarrier_injective).trans (MulEquiv.subgroupCongr hmap))
  exact ⟨t,v,ht,htR,hvQ,hvT,hv2,hmark,hmap,hSylow,hExt,h3,hnf,hC,e,fun _ => rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
