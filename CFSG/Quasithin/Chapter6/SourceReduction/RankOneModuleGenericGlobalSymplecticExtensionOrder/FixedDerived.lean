module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedCenter
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedDerived

/-!
# Eliminating the nonexceptional symplectic outer Sylow

The native fixed-Sylow commutator contains a nonidentity long-root element
when q>4. The same pure middle and endpoint comparison transports this
witness into the center of its original whole local residual, in either
orientation. This contradicts the disjointness proved for the original
outer involution selected by ambient normalizer growth. Thus S=T for n>2.

The complete nonroot involution centralizer now lies in the whole common
normalizer in every such degree. Any remaining proper inner Sylow forces
n=m=2, field order four and extension index two. The fixed Sp4(2)/A6/D8
exception and the marked three-class order comparison remain open; no
ambient order bound or completion recognition is asserted here.

Source: Aschbacher--Smith F.4.37--39, printed pp.293--294, applied to the
prepared source pair in 5.3.1--3, pp.658--659 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

private theorem marked_sylow_equiv {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    {S C : Subgroup G} (hSC : S≤C) (hs : Chapter1.IsSylowIn 2 S C)
    (e : C ≃* borel (F := F)) :
    ∃ eS : S ≃* unipotent (F := F),
      ∀ s : S, (e (inclusion hSC s)).val=(eS s).val := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C)=S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.toMonoidHom=unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.toMonoidHom) e.surjective) U)
  let eS : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  exact ⟨eS,fun _ => rfl⟩

omit [Finite G] in
private theorem fixed_derived_root_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F=2^m) (hm : 2<m)
    {S K Q : Subgroup G} (hSQ : S≤Q) (hKQ : K≤Q)
    (e : S ≃* unipotent (F := F))
    (φ : Q →* Sp F) (hφ : Function.Injective φ)
    (hφe : ∀ s : S, φ (inclusion hSQ s)=(e s).val)
    (hR : (K.subgroupOf Q).map φ=pointLocal)
    (f : G) (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F))
    (hfix : ∀ s : S, a (e s).val=(e s).val ↔ s.val ∈ centralizer ({f} : Set G)) :
    let P := S ⊓ centralizer ({f} : Set G)
    ¬ Disjoint ((_root_.commutator P).map P.subtype) ((center K).map K.subtype) := by
  let P := S ⊓ centralizer ({f} : Set G)
  let R := unipotent ⊓ a.fixedSubgroup
  obtain ⟨z,hz1,hzD,hzR⟩ :=
    SourceFusionOrder.outer_fixed_derived_meets_root hF hm a hao ha hi
  obtain ⟨u,hu,huz⟩ := hzD
  let k : R →* P := {
    toFun y := ⟨(e.symm ⟨y.val,y.property.1⟩).val,⟨(e.symm ⟨y.val,y.property.1⟩).property,
      (hfix _).mp (by
        rw [e.apply_symm_apply]
        exact (MulAut.mem_fixedSubgroup _ _).mp y.property.2)⟩⟩
    map_one' := by
      apply Subtype.ext
      exact congrArg (fun x : S => x.val) (map_one e.symm)
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg (fun x : S => x.val) (map_mul e.symm
        (⟨x.val,x.property.1⟩ : unipotent (F := F)) ⟨y.val,y.property.1⟩) }
  have hk (y : R) : φ ⟨(k y).val,hSQ (k y).property.1⟩=y.val := by
    rw [show (⟨(k y).val,hSQ (k y).property.1⟩ : Q)=
      inclusion hSQ (e.symm ⟨y.val,y.property.1⟩) from rfl,hφe,e.apply_symm_apply]
  have hder : (_root_.commutator R).map k ≤ _root_.commutator P := by
    rw [map_commutator_eq,_root_.commutator_def]
    exact commutator_mono le_top le_top
  have hxD : (k u).val ∈ (_root_.commutator P).map P.subtype :=
    mem_map_of_mem P.subtype (hder (mem_map_of_mem k hu))
  let x : Q := ⟨(k u).val,hSQ (k u).property.1⟩
  have hxz : φ x=z := (hk u).trans huz
  have hxK : x.val ∈ K := by
    have hh : φ x ∈ (K.subgroupOf Q).map φ := by
      rw [hR,hxz]
      exact map_subtype_le _ hzR
    obtain ⟨v,hv,he⟩ := hh
    exact congrArg Subtype.val (hφ he) ▸ hv
  have hxZ : x.val ∈ (center K).map K.subtype := by
    refine ⟨⟨x.val,hxK⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    apply Subtype.ext
    have hyR : φ ⟨y.val,hKQ y.property⟩ ∈ pointLocal :=
      hR ▸ mem_map_of_mem φ y.property
    obtain ⟨w,hw,hwz⟩ := hzR
    change w.val=z at hwz
    have hc := congrArg (fun x : pointLocal (F := F) => x.val)
      ((mem_center_iff.mp hw) ⟨_,hyR⟩)
    have hcQ : (⟨y.val,hKQ y.property⟩ : Q)*x=x*⟨y.val,hKQ y.property⟩ := by
      apply hφ
      simpa only [map_mul,hxz,Subgroup.coe_mul,hwz] using hc
    exact congrArg (fun q : Q => q.val) hcQ
  change ¬ Disjoint ((_root_.commutator P).map P.subtype) ((center K).map K.subtype)
  intro hd
  have hx1 : x.val=1 := mem_bot.mp (hd.le_bot ⟨hxD,hxZ⟩)
  apply hz1
  rw [←hxz,show x=1 from Subtype.ext hx1,map_one]

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


/-- When q>4, every original outer involution has a fixed inner-Sylow
commutator meeting one of the original root centers nontrivially. The native
long root is matched with the same source endpoint in either orientation. -/
theorem Preparation.symplectic_outer_fixed_derived_meets_root
    (hm2 : 2<m) (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    let P := sourceS L H ⊓ centralizer ({f.val} : Set G)
    ∃ i : Fin 2, ¬ Disjoint ((_root_.commutator P).map P.subtype)
      ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
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
    obtain ⟨eS,heS⟩ := marked_sylow_equiv hm hF hSC hs a.comparison.middle
    let α : MulAut (Sp F) := (σ fN).val
    have hα : orderOf α=2 := by
      rw [Subgroup.orderOf_coe,orderOf_injective σ hσ]
      exact (Subgroup.orderOf_coe fN).symm.trans ((Subgroup.orderOf_coe f).trans hf)
    have hαout : α ∉ MulAut.innerSubgroup (Sp F) := fun hh => hfC ((hinner fN).mp hh)
    have hfix : ∀ s : sourceS L H, α (eS s).val=(eS s).val ↔
        s.val ∈ centralizer ({f.val} : Set G) := by
      intro s
      have hnative (x : borel (F := F)) : ((a.action fN).middle x).val=α x.val := by
        have hh := congrArg (fun z => (z.middle x).val) (DFunLike.congr_fun hact fN)
        exact hh.symm
      have hconj := a.middle_conjugation fN (a.comparison.middle (inclusion hSC s))
      simp only [a.comparison.middle.symm_apply_apply] at hconj
      constructor
      · intro hfix
        have hmid : (a.action fN).middle (a.comparison.middle (inclusion hSC s)) =
            a.comparison.middle (inclusion hSC s) := by
          apply Subtype.ext
          rw [hnative,heS]
          exact hfix
        rw [hmid,a.comparison.middle.symm_apply_apply] at hconj
        exact mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp hconj.symm).symm
      · intro hfix
        have hcf : f.val*s.val*f.val⁻¹=s.val :=
          mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hfix).symm
        have hmid : (a.action fN).middle (a.comparison.middle (inclusion hSC s)) =
            a.comparison.middle (inclusion hSC s) := by
          apply a.comparison.middle.symm.injective
          apply Subtype.ext
          rw [a.comparison.middle.symm_apply_apply]
          exact hconj.trans hcf
        have hh := congrArg Subtype.val hmid
        rwa [hnative,heS] at hh
    have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i)=solvableResidual (P i) := by
      have hr := d.parabolic_residuals h hH.1.1.2 hp i
      rw [←hr]
      exact comap_map_eq_self_of_injective (P i).subtype_injective _
  · refine ⟨0,?_⟩
    apply fixed_derived_root_transport hF hm2 (hSC.trans inf_le_left)
      (show L≤P 0 from le_sup_left.trans le_sup_left) eS
      (pointParabolic.subtype.comp a.comparison.left.toMonoidHom)
      (pointParabolic.subtype_injective.comp a.comparison.left.injective) _ _
      f.val α hα (σ fN).property hαout hfix
    · intro s
      exact (congrArg Subtype.val (a.comparison.left_commutes (inclusion hSC s))).trans (heS s)
    · have hres0 : L.subgroupOf (P 0)=solvableResidual (P 0) := hres 0
      rw [hres0,←map_map,map_solvableResidual_eq a.comparison.left.toMonoidHom
        a.comparison.left.surjective]
      exact pointParabolic_solvableResidual_eq hF hm'
  · refine ⟨1,?_⟩
    apply fixed_derived_root_transport hF hm2 (hSC.trans inf_le_right)
      (show residual H≤P 1 from le_sup_left.trans le_sup_left) eS
      (pointParabolic.subtype.comp a.comparison.right.toMonoidHom)
      (pointParabolic.subtype_injective.comp a.comparison.right.injective) _ _
      f.val α hα (σ fN).property hαout hfix
    · intro s
      exact (congrArg Subtype.val (a.comparison.right_commutes (inclusion hSC s))).trans (heS s)
    · have hres1 : (residual H).subgroupOf (P 1)=solvableResidual (P 1) := hres 1
      rw [hres1,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
        a.comparison.right.surjective]
      exact pointParabolic_solvableResidual_eq hF hm'

/-- The nonexceptional symplectic field branch has no even outer part:
the original inner Sylow equals the original ambient Sylow whenever n>2. -/
theorem Preparation.symplectic_sourceS_eq_sylow_of_two_lt (hn2 : 2<n) :
    sourceS L H=(T : Subgroup G) := by
  by_contra hst
  obtain ⟨f,hf,ho,_,hdis⟩ :=
    d.symplectic_outer_fixed_derived_disjoint_roots h hH hp F hm hF he hst
  have hm2 : 2<m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1 ▸ hn2
  obtain ⟨i,hi⟩ := d.symplectic_outer_fixed_derived_meets_root h hH hp F hm hF he hm2 f hf ho
  exact hi (hdis i)

/-- Only the genuine field-four exception can retain a proper inner Sylow.
This does not exclude that final exception. -/
theorem Preparation.symplectic_proper_inner_sylow_exponent
    (hst : sourceS L H≠(T : Subgroup G)) : n=2 := by
  have hn := h.exponent
  by_contra hh
  exact hst (d.symplectic_sourceS_eq_sylow_of_two_lt h hH hp F hm hF he (by omega))

/-- For n>2 the complete ambient centralizer of a nonroot central
involution lies in the whole common normalizer, with S=T now discharged. -/
theorem Preparation.symplectic_square_centralizer_le_middle_of_two_lt (hn2 : 2<n)
    (z : sourceS L H) (hz : orderOf z=2) (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_sylow h hH hp F hm hF he
    (d.symplectic_sourceS_eq_sylow_of_two_lt h hH hp F hm hF he hn2) z hz hsq

/-- A proper inner Sylow forces precisely field order four and Sylow
extension degree two. The remaining exceptional argument must retain both. -/
theorem Preparation.symplectic_proper_inner_sylow_field_four
    (hst : sourceS L H≠(T : Subgroup G)) :
    n=2 ∧ m=2 ∧ Nat.card F=4 ∧ (sourceS L H).relIndex (T : Subgroup G)=2 := by
  have hn := d.symplectic_proper_inner_sylow_exponent h hH hp F hm hF he hst
  have hm2 : m=2 := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.trans hn
  have hd := d.symplectic_source_sylow_index_dvd h hH hp F hm hF he
  rw [hn] at hd
  have hi : (sourceS L H).relIndex (T : Subgroup G)≠1 := by
    intro hh
    exact hst (le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
      (relIndex_eq_one.mp hh))
  refine ⟨hn,hm2,?_,(Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hi⟩
  norm_num [hF,hm2]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
