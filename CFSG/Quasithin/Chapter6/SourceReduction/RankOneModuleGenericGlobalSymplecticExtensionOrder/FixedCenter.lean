module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.NormalizerGrowth
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedFlag
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Fixed-center placement for the original outer symplectic involution

The native Borel cocycle descent preserves the marked flag. The same pure
middle comparison therefore identifies the fixed inner Sylow with its native
fixed group, whose centralizer in the original Sylow is the two-root center.
The cyclic native outer quotient puts [T,T] in S. Consequently the actual
characteristic subgroup Z(C_T(f)) intersect [C_T(f),C_T(f)] lies in Z(S),
for the same f selected by the ambient normalizer-growth argument.

Applying the accepted normalizer obstruction now proves that this subgroup
avoids both original root centers, with no placement premise. Normality
and the finite two-group center theorem promote this disjointness to the
derived subgroup of the fixed inner Sylow. A nontrivial
root intersection for nonbinary fixed fields, and the fixed Sp4(2)/A6/D8
exception at q=4, still have to exclude the configuration. This does not
assert S=T or the full-extension order bound.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf,
applied to 5.3.1--3, pp.658--659. Both orientations, the original Sylow,
and the perfect whole right residual are retained.
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
private theorem fixed_center_transport {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1<m) (hF : Nat.card F=2^m)
    (S : Subgroup G) (f : G) (e : S ≃* unipotent (F := F))
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F))
    (hfix : ∀ s : S, a (e s).val=(e s).val ↔ s.val ∈ centralizer ({f} : Set G)) :
    S ⊓ centralizer ((S ⊓ centralizer ({f} : Set G) : Subgroup G) : Set G) ≤
      (center S).map S.subtype := by
  rintro x ⟨hxS,hxC⟩
  let s : S := ⟨x,hxS⟩
  have hn : (e s).val ∈ (center (unipotent (F := F))).map unipotent.subtype := by
    apply SourceFusionOrder.unipotent_centralizer_fixed_le_center hF hm a hao ha hi
    refine ⟨(e s).property,?_⟩
    intro y hy
    let t := e.symm ⟨y,hy.1⟩
    have hyt : (e t).val=y := congrArg Subtype.val (e.apply_symm_apply ⟨y,hy.1⟩)
    have ht : t.val ∈ centralizer ({f} : Set G) := (hfix t).mp (by
      rw [hyt]
      exact (MulAut.mem_fixedSubgroup a y).mp hy.2)
    have hc : t*s=s*t := Subtype.ext (hxC t.val ⟨t.property,ht⟩)
    simpa only [map_mul,Subgroup.coe_mul,hyt] using congrArg (fun z : S => (e z).val) hc
  obtain ⟨z,hz,hez⟩ := hn
  have hez' : z=e s := Subtype.ext hez
  have hsZ : s ∈ center S := by
    apply mem_center_iff.mpr
    intro t
    apply e.injective
    rw [map_mul,map_mul]
    exact mem_center_iff.mp (hez' ▸ hz) (e t)
  exact mem_map_of_mem S.subtype hsZ

private theorem normal_derived_disjoint
    (C E R : Subgroup G) (hC : IsPGroup 2 C)
    (hE : E ≤ (_root_.commutator C).map C.subtype)
    (hCN : C ≤ normalizer (E : Set G))
    (hCR : C ≤ normalizer (R : Set G))
    (hdis : Disjoint ((center C ⊓ _root_.commutator C).map C.subtype) R) :
    Disjoint E R := by
  have hEC : E ≤ C := hE.trans (map_subtype_le _)
  let K := (E ⊓ R).subgroupOf C
  have hKC : E ⊓ R ≤ C := inf_le_left.trans hEC
  have hn : C ≤ normalizer ((E ⊓ R : Subgroup G) : Set G) :=
    (le_inf hCN hCR).trans inf_normalizer_le_normalizer_inf
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  by_contra hd
  have hK : K ≠ ⊥ := by
    intro hh
    apply hd
    have hm := congrArg (Subgroup.map C.subtype) hh
    rw [map_subgroupOf_eq_of_le hKC,Subgroup.map_bot] at hm
    exact disjoint_iff.mpr hm
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK
  let : Fact (IsPGroup 2 C) := ⟨hC⟩
  obtain ⟨x,hx,hxc⟩ := exists_nontrivial_center_mem_normal (p := 2) K
  have hxE : x.val.val ∈ E := x.property.1
  have hxR : x.val.val ∈ R := x.property.2
  obtain ⟨y,hy,he⟩ := hE hxE
  have hyx : y=x.val := Subtype.ext he
  have hxZ : x.val.val ∈ (center C ⊓ _root_.commutator C).map C.subtype :=
    mem_map_of_mem C.subtype ⟨hxc,hyx ▸ hy⟩
  have hx1 : x.val.val=1 := mem_bot.mp (hdis.le_bot ⟨hxZ,hxR⟩)
  exact hx (Subtype.ext (Subtype.ext hx1))


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


/-- The fixed inner Sylow has no new centralizer inside S: its centralizer
there is the original two-root center. This uses the same outer involution,
without assuming ambient Sylow placement or S=T. -/
theorem Preparation.symplectic_inner_fixed_centralizer_le
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    sourceS L H ⊓ centralizer
      ((sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ≤
        (center (sourceS L H)).map (sourceS L H).subtype := by
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
    apply fixed_center_transport hm' hF (sourceS L H) f.val eS α hα (σ fN).property hαout
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

/-- The center of the fixed inner Sylow lies in the center of the original S. -/
theorem Preparation.symplectic_inner_fixed_center_le
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    let C := sourceS L H ⊓ centralizer ({f.val} : Set G)
    (center C).map C.subtype ≤ (center (sourceS L H)).map (sourceS L H).subtype := by
  dsimp only
  rintro x ⟨z,hz,rfl⟩
  apply d.symplectic_inner_fixed_centralizer_le h hH hp F hm hF he f hf ho
  refine ⟨z.property.1,?_⟩
  intro y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)

/-- The actual Sylow commutator is inner, via the cyclic native outer quotient. -/
theorem Preparation.symplectic_sylow_commutator_le_sourceS :
    (_root_.commutator T).map (T : Subgroup G).subtype ≤ sourceS L H := by
  obtain ⟨ρ,_,_,hi⟩ := d.symplectic_sylow_native_action h hH hp F hm hF he
  have hm' : 1<m := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1 ▸ h.exponent
  let := DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card hF hm'
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let : CommGroup (MulAut.Outer (Sp F)) := IsCyclic.commGroup
  let π := (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp ρ
  rintro _ ⟨x,hx,rfl⟩
  apply (hi x).mp
  apply (QuotientGroup.eq_one_iff _).mp
  exact Abelianization.commutator_subset_ker π hx

/-- The center-derived subgroup in F.4.37 lies in the original inner
Sylow center, for every outer involution in T, including q=4. -/
theorem Preparation.symplectic_outer_derived_center_le
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
    (center C ⊓ _root_.commutator C).map C.subtype ≤
      (center (sourceS L H)).map (sourceS L H).subtype := by
  let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  have hCS : (_root_.commutator C).map C.subtype ≤ sourceS L H := by
    have ht : (_root_.commutator C).map (inclusion (show C≤(T : Subgroup G) from inf_le_left)) ≤
        _root_.commutator T := by
      rw [map_commutator_eq,_root_.commutator_def]
      exact commutator_mono le_top le_top
    have hh := (map_mono (f := (T : Subgroup G).subtype) ht).trans
      (d.symplectic_sylow_commutator_le_sourceS h hH hp F hm hF he)
    rw [map_map] at hh
    have heq : (T : Subgroup G).subtype.comp (inclusion (show C≤(T : Subgroup G) from inf_le_left)) = C.subtype := by ext; rfl
    rwa [heq] at hh
  change (center C ⊓ _root_.commutator C).map C.subtype ≤ _
  rintro _ ⟨x,hx,rfl⟩
  apply d.symplectic_inner_fixed_centralizer_le h hH hp F hm hF he f hf ho
  refine ⟨hCS (mem_map_of_mem C.subtype hx.2),?_⟩
  intro y hy
  have hyC : y∈C := ⟨sourceS_le_sylow h.sylow_normalizes hH.1.1.2 hy.1,hy.2⟩
  exact congrArg Subtype.val ((mem_center_iff.mp hx.1) ⟨y,hyC⟩)

/-- Applying the proved placement to the same chosen outer involution
makes its characteristic center-derived subgroup disjoint from both root
centers. Nontrivial root intersection and the field-four exception remain
for the exclusion step. -/
theorem Preparation.symplectic_outer_derived_center_disjoint_roots
    (hst : sourceS L H≠(T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
      let Z := (center C ⊓ _root_.commutator C).map C.subtype
      Z ≤ (center (sourceS L H)).map (sourceS L H).subtype ∧
        ∀ i : Fin 2, Disjoint Z ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
  obtain ⟨f,hf,ho,hlocal,hZ⟩ :=
    d.symplectic_outer_derived_center_obstruction h hH hp F hm hF he hst
  have hle := d.symplectic_outer_derived_center_le h hH hp F hm hF he f hf ho
  exact ⟨f,hf,ho,hlocal,hle,hZ hle⟩
/-- The same maximal outer involution has its fixed inner-Sylow derived
subgroup disjoint from both root centers. This reduces the nonexceptional
contradiction to the native fixed group alone, without classifying the whole
extension centralizer. -/
theorem Preparation.symplectic_outer_fixed_derived_disjoint_roots
    (hst : sourceS L H≠(T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let P := sourceS L H ⊓ centralizer ({f.val} : Set G)
      ∀ i : Fin 2, Disjoint ((_root_.commutator P).map P.subtype)
        ((center (![L,residual H] i)).map (![L,residual H] i).subtype) := by
  obtain ⟨f,hf,ho,hlocal,_,hdis⟩ :=
    d.symplectic_outer_derived_center_disjoint_roots h hH hp F hm hF he hst
  refine ⟨f,hf,ho,hlocal,?_⟩
  let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
  let P := sourceS L H ⊓ centralizer ({f.val} : Set G)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hPC : P ≤ C := inf_le_inf_right _ hST
  have hTS : (T : Subgroup G) ≤ normalizer (sourceS L H : Set G) := by
    have hSP := d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he
    have hs : sourceS L H=(T : Subgroup G) ⊓ L :=
      (inf_eq_left.mpr (hSP 0)).symm.trans d.left_intersection
    rw [hs]
    exact (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hCP : C ≤ normalizer (P : Set G) :=
    (le_inf (inf_le_left.trans hTS) (inf_le_right.trans (centralizer ({f.val} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hE : (_root_.commutator P).map P.subtype ≤ (_root_.commutator C).map C.subtype := by
    have hm : (_root_.commutator P).map (inclusion hPC)≤_root_.commutator C := by
      rw [map_commutator_eq,_root_.commutator_def]
      exact commutator_mono le_top le_top
    have hh := map_mono (f := C.subtype) hm
    rw [map_map] at hh
    have heq : C.subtype.comp (inclusion hPC)=P.subtype := by ext; rfl
    rwa [heq] at hh
  dsimp only
  intro i
  apply normal_derived_disjoint C _ _ (T.isPGroup'.to_le inf_le_left) hE
    (hCP.trans (normalizer_le_normalizer_characteristic_image P (_root_.commutator P))) _ (hdis i)
  have hTJ : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
    fin_cases i
    · exact h.sylow_normalizes
    · exact hH.1.1.2.trans (le_normalizer_residual H)
  exact inf_le_left.trans (hTJ.trans
    (normalizer_le_normalizer_characteristic_image _ (center (![L,residual H] i))))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
