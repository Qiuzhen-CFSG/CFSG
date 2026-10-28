module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedDerived
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedRoot

/-!
# Root-to-outer fusion in the exceptional symplectic field-four case

Borel descent gives a unique nonidentity fixed element in the native long
root. The same endpoint comparison transports it into the original root
center in either orientation. Its uniqueness makes it central in C_T(f).
The larger ambient normalizer of C_T(f) must move it, since its full ambient
centralizer lies in the corresponding endpoint. If the moved element were
inner, fixed-center placement and root nonfusion would force it back to the
same unique element. Thus an actual original root involution is fused into
T minus S whenever S<T; the earlier exclusion already forces field order four.

These are the fixed-root and exceptional fusion steps of Aschbacher--Smith
F.4.37, printed p.293 of refs/quasithin.pdf, for the original prepared pair
of 5.3.1--3, pp.658--659. The subsequent fixed Sp4(2)/A6/D8 obstruction,
S=T at q=4, and the full marked centralizer/order comparison remain required.
No completion recognition or ambient fusion premise is used here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixed_root_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F=4)
    {K Q : Subgroup G} (hKQ : K≤Q)
    (φ : Q →* Sp F) (hφ : Function.Injective φ)
    (hR : (K.subgroupOf Q).map φ=pointLocal)
    (f : G) (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F))
    (hfix : ∀ x : Q, a (φ x)=φ x ↔ x.val ∈ centralizer ({f} : Set G)) :
    ∃ z : G, z≠1 ∧ z ∈ (center K).map K.subtype ∧
      z ∈ centralizer ({f} : Set G) ∧
      ∀ x ∈ (center K).map K.subtype, x ∈ centralizer ({f} : Set G) → x=1 ∨ x=z := by
  have hc (x : Q) : x.val ∈ (center K).map K.subtype ↔
      φ x ∈ (center (pointLocal (F := F))).map pointLocal.subtype := by
    constructor
    · rintro ⟨k,hk,hkx⟩
      change k.val=x.val at hkx
      have hxK : x.val ∈ K := hkx ▸ k.property
      refine ⟨⟨φ x,hR ▸ mem_map_of_mem φ hxK⟩,mem_center_iff.mpr ?_,rfl⟩
      intro y
      have hyR : y.val ∈ (K.subgroupOf Q).map φ := by rw [hR]; exact y.property
      obtain ⟨v,hv,he⟩ := hyR
      apply Subtype.ext
      change y.val * φ x=φ x * y.val
      rw [←he,←map_mul,←map_mul]
      apply congrArg φ
      apply Subtype.ext
      have hh := congrArg (fun k : K => k.val) ((mem_center_iff.mp hk) ⟨v.val,hv⟩)
      simpa only [Subgroup.coe_mul,hkx] using hh
    · rintro ⟨y,hy,hyx⟩
      change y.val=φ x at hyx
      have hxK : x.val ∈ K := by
        have hxR : φ x ∈ (K.subgroupOf Q).map φ := by rw [hR,←hyx]; exact y.property
        obtain ⟨v,hv,he⟩ := hxR
        exact congrArg Subtype.val (hφ he) ▸ hv
      refine ⟨⟨x.val,hxK⟩,mem_center_iff.mpr ?_,rfl⟩
      intro k
      have hkR : φ ⟨k.val,hKQ k.property⟩ ∈ pointLocal := hR ▸ mem_map_of_mem φ k.property
      have hh := congrArg (fun y : pointLocal (F := F) => y.val)
        ((mem_center_iff.mp hy) ⟨_,hkR⟩)
      have heq : (⟨k.val,hKQ k.property⟩ : Q)*x=x*⟨k.val,hKQ k.property⟩ := by
        apply hφ
        simpa only [map_mul,Subgroup.coe_mul,hyx] using hh
      exact Subtype.ext (congrArg (fun v : Q => v.val) heq)
  obtain ⟨z,hz1,hzR,haz,hunique⟩ := SourceFusionOrder.outer_fixed_root_unique hF a hao ha hi
  obtain ⟨v,_,hvz⟩ := hR.symm ▸ map_subtype_le _ hzR
  have hvR : v.val ∈ (center K).map K.subtype := (hc v).mpr (hvz.symm ▸ hzR)
  have hvf : v.val ∈ centralizer ({f} : Set G) := (hfix v).mp (by rw [hvz]; exact haz)
  refine ⟨v.val,?_,hvR,hvf,?_⟩
  · intro hh
    apply hz1
    rw [←hvz,show v=1 from Subtype.ext hh,map_one]
  · intro x hx hxf
    let xQ : Q := ⟨x,hKQ (map_subtype_le _ hx)⟩
    rcases hunique (φ xQ) ((hc xQ).mp hx) ((hfix xQ).mpr hxf) with hh | hh
    · left
      exact congrArg Subtype.val (hφ (hh.trans (map_one φ).symm))
    · right
      exact congrArg Subtype.val (hφ (hh.trans hvz.symm))

omit [Finite G] in
private theorem endpoint_fixed
    {F : Type*} [Field F] {Q : Subgroup G} {R : Subgroup (Sp F)}
    (e : Q ≃* R) (b : MulAut R) (a : MulAut (Sp F)) (f : G)
    (hb : ∀ y, (b y).val=a y.val)
    (hc : ∀ y, (e.symm (b y)).val=f*(e.symm y).val*f⁻¹) (x : Q) :
    a (e x).val=(e x).val ↔ x.val ∈ centralizer ({f} : Set G) := by
  have hh := hc (e x)
  rw [e.symm_apply_apply] at hh
  constructor
  · intro hx
    have he : b (e x)=e x := Subtype.ext ((hb _).trans hx)
    rw [he,e.symm_apply_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hx
    have hfx : f*x.val*f⁻¹=x.val :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx).symm
    have he : b (e x)=e x := by
      apply e.symm.injective
      apply Subtype.ext
      rw [e.symm_apply_apply]
      exact hh.trans hfx
    exact (hb _).symm.trans (congrArg Subtype.val he)

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he


/-- At q=4 every original outer involution has exactly one nonidentity
fixed element in one of the two original root centers. Both orientations
use the point endpoint of the same native action. -/
theorem Preparation.symplectic_outer_fixed_root_unique
    (hq : Nat.card F=4) (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, z≠1 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      z ∈ centralizer ({f.val} : Set G) ∧
      ∀ x ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
        x ∈ centralizer ({f.val} : Set G) → x=1 ∨ x=z := by
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hTN : (T : Subgroup G)≤N :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  let fN : N := inclusion hTN f
  have hSC : sourceS L H≤C :=
    le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hFC := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hFC]
    exact hFC.sylow_commonBorel
  have hfC : f.val ∉ C := by
    intro hfc
    obtain ⟨R,hR⟩ := hs
    have hRT : (R : Subgroup C)≤(T : Subgroup G).subgroupOf C := by
      intro x hx
      exact hST (hR ▸ mem_map_of_mem C.subtype hx)
    have hTR : (T : Subgroup G).subgroupOf C=R :=
      R.is_maximal' (T.isPGroup'.comap_subtype (K := C)) hRT
    apply ho
    apply hR ▸ mem_map_of_mem C.subtype (x := (⟨f.val,hfc⟩ : C))
    rw [←hTR]
    exact f.property
  obtain ⟨hmn,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  have hm' : 1<m := hmn ▸ h.exponent
  rcases hlift with ⟨a,σ,hσ,hact,_,hinner⟩ | ⟨a,σ,hσ,hact,_,hinner⟩
  all_goals
    let α : MulAut (Sp F) := (σ fN).val
    have hα : orderOf α=2 := by
      rw [Subgroup.orderOf_coe,orderOf_injective σ hσ]
      exact (Subgroup.orderOf_coe fN).symm.trans ((Subgroup.orderOf_coe f).trans hf)
    have hαout : α ∉ MulAut.innerSubgroup (Sp F) := fun hh => hfC ((hinner fN).mp hh)
    have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i)=solvableResidual (P i) := by
      rw [←d.parabolic_residuals h hH.1.1.2 hp i]
      exact comap_map_eq_self_of_injective (P i).subtype_injective _
  · refine ⟨0,?_⟩
    refine fixed_root_transport hq (show L≤P 0 from le_sup_left.trans le_sup_left)
      (pointParabolic.subtype.comp a.comparison.left.toMonoidHom)
      (pointParabolic.subtype_injective.comp a.comparison.left.injective) ?_
      f.val α hα (σ fN).property hαout ?_
    · have hr : L.subgroupOf (P 0)=solvableResidual (P 0) := hres 0
      rw [hr,←map_map,map_solvableResidual_eq a.comparison.left.toMonoidHom
        a.comparison.left.surjective]
      exact pointParabolic_solvableResidual_eq hF hm'
    · intro x
      apply endpoint_fixed a.comparison.left (a.action fN).left α f.val _
        (a.left_conjugation fN) x
      intro y
      exact (congrArg (fun z => (z.left y).val) (DFunLike.congr_fun hact fN)).symm
  · refine ⟨1,?_⟩
    refine fixed_root_transport hq (show residual H≤P 1 from le_sup_left.trans le_sup_left)
      (pointParabolic.subtype.comp a.comparison.right.toMonoidHom)
      (pointParabolic.subtype_injective.comp a.comparison.right.injective) ?_
      f.val α hα (σ fN).property hαout ?_
    · have hr : (residual H).subgroupOf (P 1)=solvableResidual (P 1) := hres 1
      rw [hr,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
        a.comparison.right.surjective]
      exact pointParabolic_solvableResidual_eq hF hm'
    · intro x
      apply endpoint_fixed a.comparison.right (a.action fN).right α f.val _
        (a.right_conjugation fN) x
      intro y
      exact (congrArg (fun z => (z.right y).val) (DFunLike.congr_fun hact fN)).symm

private theorem root_center_le_source_center (i : Fin 2) :
    (center (![L,residual H] i)).map (![L,residual H] i).subtype ≤
      (center (sourceS L H)).map (sourceS L H).subtype := by
  have hFC := d.hypothesisF11 h hH.1.1.2
  have hSK := d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  obtain ⟨R,hR⟩ := hFC.sylow i
  rw [inf_eq_left.mpr (hSK i)] at hR
  rintro _ ⟨z,hz,rfl⟩
  have hzcore : z ∈ pCore 2 (![L,residual H] i) :=
    hFC.local_core_selfCentralizing i (center_le_centralizer _ hz)
  have hzS : z.val ∈ sourceS L H := hR ▸
    (pCoreIn_le_sylow (![L,residual H] i) R) (mem_map_of_mem _ hzcore)
  refine ⟨⟨z.val,hzS⟩,mem_center_iff.mpr ?_,rfl⟩
  intro s
  exact Subtype.ext (congrArg (fun x : ![L,residual H] i => x.val)
    ((mem_center_iff.mp hz) ⟨s.val,hSK i s.property⟩))

/-- A proper inner Sylow forces genuine ambient fusion from an original
root involution into T minus S. This is the exceptional Sp4(4) fusion step
of F.4.37, with the actual ambient conjugator retained. -/
theorem Preparation.symplectic_proper_inner_sylow_outer_root_fusion
    (hst : sourceS L H≠(T : Subgroup G)) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧ IsConj z t.val := by
  have hq := (d.symplectic_proper_inner_sylow_field_four h hH hp F hm hF he hst).2.2.1
  obtain ⟨f,hf,ho,_,V,_,_,_,hVN,hout,_⟩ :=
    d.symplectic_outer_centralizer_normalizer_growth h hH hp F hm hF he hst
  obtain ⟨i,z,hz1,hzR,hzf,hunique⟩ :=
    d.symplectic_outer_fixed_root_unique h hH hp F hm hF he hq f hf ho
  let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hZle := root_center_le_source_center d h hH hp F hm hF he i
  have hzZ := hZle hzR
  have hzS := map_subtype_le _ hzZ
  have hzC : z ∈ C := ⟨hST hzS,hzf⟩
  have hz2 : orderOf z=2 := by
    let := (d.symplectic_root_center_fusion h hH hp F hm hF he i).1
    have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2
        ((center (![L,residual H] i)).map (![L,residual H] i).subtype))
      (⟨z,hzR⟩ : (center (![L,residual H] i)).map (![L,residual H] i).subtype)
    apply orderOf_eq_prime _ hz1
    exact congrArg Subtype.val hpow
  have hTZ : (T : Subgroup G) ≤ normalizer
      ((center (![L,residual H] i)).map (![L,residual H] i).subtype : Set G) := by
    rw [(d.symplectic_root_center_fusion h hH hp F hm hF he i).2.2]
    fin_cases i
    · exact h.sylow_normalizes
    · exact hH.1.1.2.trans (le_normalizer_residual H)
  have hzcenter : (⟨z,hzC⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    have hyzR := (hTZ y.property.1 z).mp hzR
    have hyzf : y.val*z*y.val⁻¹ ∈ centralizer ({f.val} : Set G) :=
      (centralizer ({f.val} : Set G)).mul_mem
        ((centralizer ({f.val} : Set G)).mul_mem y.property.2 hzf)
        ((centralizer ({f.val} : Set G)).inv_mem y.property.2)
    have hyz1 : y.val*z*y.val⁻¹≠1 := (MulAut.conj y.val).map_ne_one_iff.mpr hz1
    have heq := (hunique _ hyzR hyzf).resolve_left hyz1
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp heq)
  have hzbound := d.symplectic_central_involution_centralizers h hH hp F hm hF he i z hzR hz2
  have hnot : ¬ V ≤ centralizer ({z} : Set G) := fun hh => hout i (hh.trans hzbound)
  obtain ⟨g,hg,hgz⟩ := SetLike.not_le_iff_exists.mp hnot
  let t := g*z*g⁻¹
  have htC : t∈C := (hVN hg z).mp hzC
  have htZ : t ∈ (center C).map C.subtype :=
    ((normalizer_le_normalizer_characteristic_image C (center C)) (hVN hg) z).mp
      (mem_map_of_mem C.subtype hzcenter)
  have ht1 : t≠1 := (MulAut.conj g).map_ne_one_iff.mpr hz1
  have htz : t≠z := by
    intro hh
    exact hgz (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh))
  have htS : t ∉ sourceS L H := by
    intro ht
    have htZS : t ∈ (center (sourceS L H)).map (sourceS L H).subtype := by
      apply d.symplectic_inner_fixed_centralizer_le h hH hp F hm hF he f hf ho
      refine ⟨ht,?_⟩
      intro y hy
      obtain ⟨v,hv,hvt⟩ := htZ
      change v.val=t at hvt
      have hyC : y∈C := ⟨hST hy.1,hy.2⟩
      simpa only [Subgroup.coe_mul,hvt] using
        congrArg Subtype.val ((mem_center_iff.mp hv) ⟨y,hyC⟩)
    obtain ⟨zs,hzs,hzse⟩ := hzZ
    obtain ⟨ts,hts,htse⟩ := htZS
    change zs.val=z at hzse
    change ts.val=t at htse
    have hconj : IsConj zs.val ts.val := by
      rw [hzse,htse]
      exact isConj_iff.mpr ⟨g,rfl⟩
    have htR := (d.symplectic_root_center_nonfusion h hH hp F hm hF he
      i zs ts hzs hts hconj).mp (hzse.symm ▸ hzR)
    rw [htse] at htR
    exact (hunique t htR htC.2).elim ht1 htz
  refine ⟨i,z,hz2,hzR,⟨t,htC.1⟩,?_,htS,isConj_iff.mpr ⟨g,rfl⟩⟩
  exact (Subgroup.orderOf_coe (⟨t,htC.1⟩ : T)).symm.trans
    (((MulAut.conj g).orderOf_eq z).trans hz2)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
