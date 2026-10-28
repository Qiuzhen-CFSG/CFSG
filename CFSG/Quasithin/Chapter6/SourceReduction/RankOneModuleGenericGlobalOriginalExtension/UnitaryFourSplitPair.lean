module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphAction
public import Theory.GroupTheory.Amalgam.SplitExtension

/-!
# Both full endpoint squares for the original U₄ degree-two extension

The actual source involution splits both original endpoints over their
O²-subgroups. The original inner markings identify these subgroups exactly;
agreement in the full overlap then proves that the same involution also
splits the entire common Borel, including its odd part. Multiplication gives
one compatible pair of semidirect-product isomorphisms.

Transport through the existing reduced comparison gives an action on the
native point and plane parabolics. Both endpoint actions and the full middle
action are proved to be restrictions of the same original ambient native
automorphism. That automorphism is an outer involution. The already constructed
conjugate graph action on the entire L is retained by the same split comparison.
No equality S=T or R=O²(H) is used; arbitrary selected perfect R, either
orientation and q=4 are retained.

This constructs the full split pair for the transported action. Identifying
that action with the prescribed native graph extension, and hence obtaining
ConcreteAmalgamComparison, remains necessary. The Chapter 12 application
consumes genuine reduced DGS restoration and the completed ordinary branch.
DGS exhaustion, prepared U₅, uniqueness and unconditional GlobalExit remain.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6--7, pp.650--651
(`refs/quasithin.pdf`). The false printed O₂(overlap) identity is not used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))

private theorem inner_preimage {Y X : Type*} [Group Y] [Group X]
    (D P : Subgroup Y) (hle : D ≤ P) (f : P →* MulAut X)
    (hf : Function.Injective f) (Q : Subgroup X)
    (hbase : f.range ⊓ MulAut.innerSubgroup X = Q.map MulAut.conj)
    (hr : (f.comp (inclusion hle)).range = Q.map MulAut.conj)
    (x : P) : f x ∈ MulAut.innerSubgroup X ↔ x.val ∈ D := by
  constructor
  · intro hx
    have hm : f x ∈ (f.comp (inclusion hle)).range := hr.symm ▸ hbase.le ⟨⟨x,rfl⟩,hx⟩
    obtain ⟨y,hy⟩ := hm
    have he : (inclusion hle y : P)=x := hf hy
    exact congrArg Subtype.val he ▸ y.property
  · intro hx
    have hm : f x ∈ Q.map MulAut.conj := hr ▸ (show f x ∈ (f.comp (inclusion hle)).range from
      ⟨⟨x.val,hx⟩,rfl⟩)
    exact (hbase.ge hm).2

include d h hTH hp mark in
theorem original_unitaryFour_reduced_left_iff_inner
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    mark.left x ∈ MulAut.innerSubgroup (ProjectiveGroup m hm) ↔
      x.val ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 :=
  inner_preimage _ _ (d.originalUnitaryFour_reduced_le h hTH hp m hm point mark 0)
    mark.left mark.left_injective _ mark.left_base
    (d.original_unitaryFour_reduced_images h hTH hp m hm point mark).1 x

include d h hTH hp mark in
theorem original_unitaryFour_reduced_right_iff_inner
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    mark.right x ∈ MulAut.innerSubgroup (ProjectiveGroup m hm) ↔
      x.val ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1 :=
  inner_preimage _ _ (d.originalUnitaryFour_reduced_le h hTH hp m hm point mark 1)
    mark.right mark.right_injective _ mark.right_base
    (d.original_unitaryFour_reduced_images h hTH hp m hm point mark).2 x

include d h hTH hp mark in
theorem original_unitaryFour_source_reduced_iff (t : sourceS L H) (i : Fin 2) :
    t.val ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i ↔ t.val ∈ L := by
  have he := d.original_unitaryFour_inner_iff h hTH hp m hm point mark t
  have hiff := he.1.trans he.2
  fin_cases i
  · have hh := d.original_unitaryFour_reduced_left_iff_inner h hTH hp m hm point mark
      (⟨t.val,(show sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from
          le_sup_right.trans le_sup_left) t.property⟩ :
        ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)
    rw [mark.sylowHom_left] at hiff
    exact hh.symm.trans hiff
  · exact (d.original_unitaryFour_reduced_right_iff_inner h hTH hp m hm point mark
      ⟨t.val,(show sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 from
        le_sup_right.trans le_sup_left) t.property⟩).symm.trans hiff

include d h hTH hp mark in
theorem original_unitaryFour_reduced_normalizes (i : Fin 2) :
    ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≤
      normalizer (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i : Set G) := by
  rw [d.original_unitaryFour_reduced_parabolics h hTH hp m hm point mark i]
  have hn := (pResidual 2 (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).le_normalizer_map
    (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype
  simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using hn

include d h hTH hp mark in
theorem original_unitaryFour_reduced_sup_source (i : Fin 2) :
    ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i ⊔ sourceS L H =
      ChapterF.Source.parabolic ![L,R] (sourceS L H) i := by
  obtain ⟨P,hP⟩ := (d.hypothesisF11 h hTH).sylow_parabolic i
  have he := congrArg (Subgroup.map (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype)
    (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype] at he
  rw [d.original_unitaryFour_reduced_parabolics h hTH hp m hm point mark i]
  exact he

private theorem involution_disjoint {X : Type*} [Group X] [Finite X] (D : Subgroup X)
    (t : X) (ht : orderOf t=2) (hout : t ∉ D) : Disjoint D (zpowers t) := by
  classical
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hx,hxt⟩
  change x ∈ D at hx
  change x ∈ zpowers t at hxt
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at hxt
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hxt
  have hk2 := Finset.mem_range.mp hk
  interval_cases k
  · simp
  · exact (hout (by simpa only [pow_one] using hx)).elim

private theorem involution_complement {X : Type*} [Group X] [Finite X]
    (D : Subgroup X) (hi : D.index=2) (t : X) (ht : orderOf t=2) (hout : t ∉ D) :
    D.IsComplement' (zpowers t) :=
  isComplement'_of_card_mul_and_disjoint
    (by rw [Nat.card_zpowers,ht,←hi,D.card_mul_index]) (involution_disjoint D t ht hout)

include d h hTH hp mark in
theorem original_unitaryFour_split_endpoints
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) (i : Fin 2) :
    let D := ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i
    D ⊔ zpowers t.val = ChapterF.Source.parabolic ![L,R] (sourceS L H) i ∧
      Disjoint D (zpowers t.val) ∧ zpowers t.val ≤ normalizer (D : Set G) := by
  let S₀ := (T : Subgroup G) ⊓ L
  have hS₀ : S₀ ≤ sourceS L H := d.left_intersection.ge.trans inf_le_left
  have hgen : S₀ ⊔ zpowers t.val = sourceS L H := by
    have hc := involution_complement
      (S₀.subgroupOf (sourceS L H)) hi t ((Subgroup.orderOf_coe t).symm.trans ht)
      (fun hx => hout hx.2)
    have he := congrArg (Subgroup.map (sourceS L H).subtype) hc.sup_eq_top
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hS₀,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,coe_subtype] using he
  have hCD : zpowers t.val ≤ sourceS L H := zpowers_le.mpr t.property
  have hD₀ : S₀ ≤ ChapterF.Source.parabolic ![L,R] S₀ i := le_sup_right.trans le_sup_left
  refine ⟨?_,involution_disjoint _ t.val ht (fun he => hout
    ((d.original_unitaryFour_source_reduced_iff h hTH hp m hm point mark t i).mp he)),?_⟩
  · calc
      _ = (ChapterF.Source.parabolic ![L,R] S₀ i ⊔ S₀) ⊔ zpowers t.val := by
        rw [sup_eq_left.mpr hD₀]
      _ = ChapterF.Source.parabolic ![L,R] S₀ i ⊔ sourceS L H := by rw [sup_assoc,hgen]
      _ = _ := d.original_unitaryFour_reduced_sup_source h hTH hp m hm point mark i
  · exact (hCD.trans (le_sup_right.trans le_sup_left)).trans
      (d.original_unitaryFour_reduced_normalizes h hTH hp m hm point mark i)

include d h hTH hp mark in
theorem original_unitaryFour_reduced_overlap
    {x : G}
    (hx : x ∈ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    x ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ↔
      x ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1 := by
  rw [←d.original_unitaryFour_reduced_left_iff_inner h hTH hp m hm point mark ⟨x,hx.1⟩,
    ←d.original_unitaryFour_reduced_right_iff_inner h hTH hp m hm point mark ⟨x,hx.2⟩]
  exact congrArg (fun a => a ∈ MulAut.innerSubgroup (ProjectiveGroup m hm))
    (mark.agrees ⟨x,hx⟩) |> Iff.of_eq

include d h hTH hp mark in
theorem original_unitaryFour_split_overlap
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) :
    (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) ⊔ zpowers t.val =
    ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 := by
  let D i := ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i
  let P i := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let C := zpowers t.val
  have hc (i : Fin 2) : C ≤ P i := (zpowers_le.mpr t.property).trans (le_sup_right.trans le_sup_left)
  have hd (i : Fin 2) : D i ≤ P i := d.originalUnitaryFour_reduced_le h hTH hp m hm point mark i
  apply le_antisymm (sup_le (inf_le_inf (hd 0) (hd 1)) (le_inf (hc 0) (hc 1)))
  intro x hx
  obtain ⟨hgen,_,hn⟩ := d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht 0
  have hxprod : x ∈ (D 0 : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,hgen]
    exact hx.1
  obtain ⟨a,ha,c,hc',he⟩ := hxprod
  have haP : a ∈ P 1 := by
    have hh := (P 1).mul_mem hx.2 ((P 1).inv_mem (hc 1 hc'))
    rw [←he,mul_inv_cancel_right] at hh
    exact hh
  have haD : a ∈ D 1 :=
    (d.original_unitaryFour_reduced_overlap h hTH hp m hm point mark ⟨hd 0 ha,haP⟩).mp ha
  rw [←he]
  exact mul_mem_sup ⟨ha,haD⟩ hc'

/-- The same actual involution acts on both whole reduced endpoints and
their entire intersection. -/
@[expose] def originalUnitaryFourPairAction
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) :=
  RankTwoAmalgam.conjugationAction
    (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0)
    (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) (zpowers t.val)
    (d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht 0).2.2
    (d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht 1).2.2

/-- Multiplication by the same source complement recognizes the whole
original pair, with both full-overlap inclusion squares. -/
def originalUnitaryFourSplitPair
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.semidirect
        (d.originalUnitaryFourPairAction h hTH hp m hm point mark hi t hout ht))
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  let D i := ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i
  let C := zpowers t.val
  have hsplit i := d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht i
  let e := RankTwoAmalgam.splitIso (D 0) (D 1) C (hsplit 0).2.2 (hsplit 1).2.2
    (hsplit 0).2.1 (hsplit 1).2.1
  let f : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (D 0 ⊔ C) ((D 0 ⊓ D 1) ⊔ C) (D 1 ⊔ C)
        (sup_le_sup_right inf_le_left C) (sup_le_sup_right inf_le_right C))
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) :=
    { left := MulEquiv.subgroupCongr (hsplit 0).1
      middle := MulEquiv.subgroupCongr
        (d.original_unitaryFour_split_overlap h hTH hp m hm point mark hi t hout ht)
      right := MulEquiv.subgroupCongr (hsplit 1).1
      left_commutes _ := rfl
      right_commutes _ := rfl }
  exact e.trans f

/-- The constructed action in the SAME native reduced coordinates. -/
@[expose] def originalUnitaryFourNativePairAction
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) :=
  (RankTwoAmalgam.automorphismConjEquiv
    (d.originalUnitaryFourReducedComparison h hTH hp m hm point mark)).toMonoidHom.comp
      (d.originalUnitaryFourPairAction h hTH hp m hm point mark hi t hout ht)

/-- The full original amalgam is a split degree-two extension of the native
pair by the action of the actual source involution. The action is constructed,
not supplied as an additional recognition hypothesis. -/
def originalUnitaryFourNativeSplitComparison
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2) :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (RankTwoAmalgam.semidirect
        (d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht)) :=
  (d.originalUnitaryFourSplitPair h hTH hp m hm point mark hi t hout ht).symm.trans
    (RankTwoAmalgam.semidirectIso
      (d.originalUnitaryFourReducedComparison h hTH hp m hm point mark)
      (d.originalUnitaryFourPairAction h hTH hp m hm point mark hi t hout ht))

private theorem marked_conjugation {Y X : Type*} [Group Y] [Group X]
    (D P : Subgroup Y) (hDP : D ≤ P) (Q : Subgroup X)
    (e : D ≃* Q) (f : P →* MulAut X)
    (hj : Function.Injective (MulAut.conj : X →* MulAut X))
    (he : ∀ x : D, MulAut.conj (e x).val=f (inclusion hDP x))
    (s : P) (hs : s.val ∈ normalizer (D : Set Y)) (x : D) :
    (e (D.normalizerMonoidHom ⟨s.val,hs⟩ x)).val=f s (e x).val := by
  apply hj
  rw [he]
  have hh : (inclusion hDP (D.normalizerMonoidHom ⟨s.val,hs⟩ x) : P) =
      s * inclusion hDP x * s⁻¹ := rfl
  rw [hh,map_mul,map_mul,map_inv,←he]
  ext z
  simp

variable (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
  (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2)

/-- On every native left endpoint element, the constructed action is the
restriction of the literal original marking, including its odd part. -/
theorem originalUnitaryFourNativePairAction_left
    (c : zpowers t.val) (x : OriginalUnitaryFour.endpoint m hm point) :
    ((d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht c).left x).val =
      mark.sylowHom ⟨c.val,(zpowers_le.mpr t.property) c.property⟩ x.val := by
  let e := d.originalUnitaryFourReducedComparison h hTH hp m hm point mark
  let s : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 :=
    ⟨c.val,(show sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from
      le_sup_right.trans le_sup_left) ((zpowers_le.mpr t.property) c.property)⟩
  have hn := (d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht 0).2.2 c.property
  have he := marked_conjugation _ _
    (d.originalUnitaryFour_reduced_le h hTH hp m hm point mark 0) _ e.left mark.left
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm)
    (d.originalUnitaryFourReducedComparison_left_apply h hTH hp m hm point mark) s hn (e.left.symm x)
  rw [e.left.apply_symm_apply] at he
  exact he.trans (congrArg (fun a : MulAut (ProjectiveGroup m hm) => a x.val)
    (mark.sylowHom_left ⟨c.val,(zpowers_le.mpr t.property) c.property⟩).symm)

/-- The SAME native automorphism gives the entire right endpoint action,
not merely the right residual quotient action. -/
theorem originalUnitaryFourNativePairAction_right
    (c : zpowers t.val) (x : OriginalUnitaryFour.endpoint m hm (!point)) :
    ((d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht c).right x).val =
      mark.sylowHom ⟨c.val,(zpowers_le.mpr t.property) c.property⟩ x.val := by
  let e := d.originalUnitaryFourReducedComparison h hTH hp m hm point mark
  let s : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 :=
    ⟨c.val,(show sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 from
      le_sup_right.trans le_sup_left) ((zpowers_le.mpr t.property) c.property)⟩
  have hn := (d.original_unitaryFour_split_endpoints h hTH hp m hm point mark hi t hout ht 1).2.2 c.property
  have he := marked_conjugation _ _
    (d.originalUnitaryFour_reduced_le h hTH hp m hm point mark 1) _ e.right mark.right
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm)
    (d.originalUnitaryFourReducedComparison_right_apply h hTH hp m hm point mark) s hn (e.right.symm x)
  rw [e.right.apply_symm_apply] at he
  exact he

/-- The whole overlap action has the same native extension, with all odd
elements retained. -/
theorem originalUnitaryFourNativePairAction_middle
    (c : zpowers t.val)
    (x : (OriginalUnitaryFour.endpoint m hm point ⊓ OriginalUnitaryFour.endpoint m hm (!point) :
      Subgroup (ProjectiveGroup m hm))) :
    ((d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht c).middle x).val =
      mark.sylowHom ⟨c.val,(zpowers_le.mpr t.property) c.property⟩ x.val := by
  have hh := congrArg Subtype.val
    ((d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht c).left_commutes x)
  exact hh.symm.trans (d.originalUnitaryFourNativePairAction_left h hTH hp m hm point mark hi t hout ht c
    (inclusion inf_le_left x))

theorem originalUnitaryFourNativeSplitComparison_left
    (x : _) :
    ((d.originalUnitaryFourNativeSplitComparison h hTH hp m hm point mark hi t hout ht).symm.left x).val =
      ((d.originalUnitaryFourReducedComparison h hTH hp m hm point mark).left.symm x.left).val * x.right.val := by
  rfl

theorem originalUnitaryFourNativeSplitComparison_right
    (x : _) :
    ((d.originalUnitaryFourNativeSplitComparison h hTH hp m hm point mark hi t hout ht).symm.right x).val =
      ((d.originalUnitaryFourReducedComparison h hTH hp m hm point mark).right.symm x.left).val * x.right.val := by
  rfl

theorem originalUnitaryFourNativeSplitComparison_middle
    (x : _) :
    ((d.originalUnitaryFourNativeSplitComparison h hTH hp m hm point mark hi t hout ht).symm.middle x).val =
      ((d.originalUnitaryFourReducedComparison h hTH hp m hm point mark).middle.symm x.left).val * x.right.val := by
  rfl

/-- The constructed three-component action extends to the SAME native
ambient automorphisms supplied by the original marking. -/
theorem originalUnitaryFourNativePairAction_extension :
    d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht =
      (Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.restriction
        (OriginalUnitaryFour.endpoint m hm point) (OriginalUnitaryFour.endpoint m hm (!point))
        (OriginalUnitaryFour.endpoint m hm point ⊓ OriginalUnitaryFour.endpoint m hm (!point))
        inf_le_left inf_le_right rfl).comp
        ((mark.sylowFlagHom (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm)).comp
          (inclusion (zpowers_le.mpr t.property))) := by
  apply MonoidHom.ext
  intro c
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact d.originalUnitaryFourNativePairAction_left h hTH hp m hm point mark hi t hout ht c x
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact d.originalUnitaryFourNativePairAction_middle h hTH hp m hm point mark hi t hout ht c x
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact d.originalUnitaryFourNativePairAction_right h hTH hp m hm point mark hi t hout ht c x

include d h hTH hp hout ht in
/-- The ambient native actor retained by all three action equations is
an actual outer involution. -/
theorem original_unitaryFour_split_actor :
    orderOf (mark.sylowHom t)=2 ∧
      mark.sylowHom t ∉ MulAut.innerSubgroup (ProjectiveGroup m hm) := by
  refine ⟨(orderOf_injective mark.sylowHom mark.sylowHom_injective t).trans
    ((Subgroup.orderOf_coe t).symm.trans ht),?_⟩
  intro hh
  have he := d.original_unitaryFour_inner_iff h hTH hp m hm point mark t
  exact hout (he.2.mp (he.1.mp hh))

omit t hout ht in
include d h hTH hp mark in
/-- The already constructed source involution gives the full split native
comparison and retains its conjugate graph action on the entire L. -/
theorem original_unitaryFour_full_split_pair (a : L ≃* L2 m hm) :
    ∃ (t : sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2),
      Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (RankTwoAmalgam.semidirect
          (d.originalUnitaryFourNativePairAction h hTH hp m hm point mark hi t hout ht))) ∧
      ∃ c : (L ⊔ sourceS L H : Subgroup G),
        originalUnitaryFourResidualAction h hTH m hm a (inclusion le_sup_right t) =
          originalUnitaryFourResidualAction h hTH m hm a c * Extension.L2Aut m hm *
            (originalUnitaryFourResidualAction h hTH m hm a c)⁻¹ := by
  obtain ⟨t,hout,ht,c,hc⟩ := d.original_unitaryFour_source_full_graph_involution
    h hTH hp m hm point mark a hi
  exact ⟨t,hout,ht,⟨d.originalUnitaryFourNativeSplitComparison h hTH hp m hm point mark hi t hout ht⟩,c,hc⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
