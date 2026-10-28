module

public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.Source
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head

/-!
# The genuine MS reduction in the natural-point case of C.1.37

The Baumann subgroup has the full point-radical image. Its join J with O²(G)
is normal because the point parabolic normalizes it and supplements O²(G).
B.2.19 places O₂(J) in the Baumann subgroup. The point parabolic inside J
has index seven and its actual two-core is exactly that Baumann subgroup.

Three explicit root displacements prove [V,O²(G)]=V. Thus V lies in J and
its centralizer there is O₂(J), giving F*(J)=O₂(J). A characteristic subgroup
of the Baumann subgroup normal in J is normalized by the point parabolic
and hence by G. In the absence of this original characteristic obstruction,
all fields of the literal binary MS input are constructed on the original
subgroups. The quotient marking remains the given quotient projection.

The original natural V also lies in the actual MS commutator core, providing
the inclusion needed to compare its marking with a later doubled-core model.
No MS classification alternative or module identification is assumed.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and C.1.31(MS1--3),
printed pp.135--136. The full C.1.34 classification remains a separate source.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open ChapterB ChapterB.BaumannArgument Theory.GroupTheory
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
  [IsElementaryAbelian 2 V]
namespace NaturalAction
variable (d : NaturalAction V)

noncomputable abbrev B : Subgroup G := baumann d.R
noncomputable abbrev J : Subgroup G := pResidual 2 G ⊔ d.B

omit [IsElementaryAbelian 2 V] in
theorem normalizes_R : d.P ≤ normalizer (d.R : Set G) := by
  rw [d.R_eq_parabolic_core]
  exact d.P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.P (pCore 2 d.P))

omit [IsElementaryAbelian 2 V] in
theorem normalizes_B : d.P ≤ normalizer (d.B : Set G) :=
  d.normalizes_R.trans (normalizer_le_normalizer_baumann d.R)

omit [IsElementaryAbelian 2 V] in
theorem residual_sup_P : pResidual 2 G ⊔ d.P = ⊤ := by
  have hm : (pResidual 2 G ⊔ d.P).map d.q = ⊤ := by
    rw [Subgroup.map_sup,d.residual_image,top_sup_eq]
  have hk : d.q.ker ≤ d.P := by
    intro g hg
    change d.q g ∈ pointParabolicSL
    rw [show d.q g = 1 from hg]
    exact one_mem _
  have he := congrArg (fun A : Subgroup SL => A.comap d.q) hm
  simpa only [comap_map_eq,comap_top,sup_eq_left.mpr (hk.trans le_sup_right)] using he

omit [IsElementaryAbelian 2 V] in
theorem J_normal : d.J.Normal := by
  apply normalizer_eq_top_iff.mp
  apply eq_top_iff.mpr
  rw [← d.residual_sup_P]
  apply sup_le (le_sup_left.trans le_normalizer)
  exact (le_inf (by rw [normalizer_eq_top]; exact le_top) d.normalizes_B).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [IsElementaryAbelian 2 V] in
theorem core_J : pCore 2 d.J = (pCore 2 G).comap d.J.subtype :=
  pCore_subnormal_eq_comap 2 d.J_normal.isSubnormal

omit [Finite G] in
private theorem map_conjugate {H : Type*} [Group H] (q : G →* H)
    (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem maxJ_le_B : elementaryAbelianMaxJ d.R ≤ d.B := by
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro z hz
  obtain ⟨zJ,hzJ,rfl⟩ := hz
  obtain ⟨zC,_,rfl⟩ := hzJ
  exact congrArg Subtype.val ((mem_center_iff.mp zC.property) ⟨j,hj⟩).symm

theorem B_image (hne : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥) :
    d.B.map d.q = pointV := by
  have hJ : elementaryAbelianMaxJ (d.D 0) ≤ elementaryAbelianMaxJ d.R := by
    apply (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ d.D_zero_le_R).2
    rw [maxOrder_eq_two_pow_rank,maxOrder_eq_two_pow_rank,d.D_zero_rank]
  have hroot : PointOffenders.root 0 ∈ d.B.map d.q := by
    apply (map_mono (hJ.trans d.maxJ_le_B))
    rw [d.thompson_D_zero_image hne]
    exact mem_zpowers _
  apply le_antisymm (map_le_iff_le_comap.mpr inf_le_left)
  intro x hx
  obtain ⟨a,rfl⟩ := show x ∈ PointOffenders.row.range from PointOffenders.row_range.symm ▸ hx
  by_cases ha : a.toAdd = 0
  · have h1 : a = 1 := ha
    rw [h1,PointOffenders.row.map_one]
    exact one_mem _
  · obtain ⟨l,hl⟩ := d.residual_surjective (PointOffenders.rowConjugator a.toAdd)
    have hlP : (l:G) ∈ d.P := by
      change d.q l ∈ pointParabolicSL
      rw [show d.q l = PointOffenders.rowConjugator a.toAdd from hl]
      exact PointOffenders.rowConjugator_mem _
    have hn := mem_normalizer_iff_map_conj_eq.mp (d.normalizes_B hlP)
    have hm := congrArg (fun A : Subgroup G => A.map d.q) hn
    change (d.B.map (MulAut.conj (l:G)).toMonoidHom).map d.q = d.B.map d.q at hm
    rw [map_conjugate,show d.q l = PointOffenders.rowConjugator a.toAdd from hl] at hm
    have hh := hm ▸ mem_map_of_mem
      (MulAut.conj (PointOffenders.rowConjugator a.toAdd)).toMonoidHom hroot
    change MulAut.conj (PointOffenders.rowConjugator a.toAdd) (PointOffenders.root 0)
      ∈ d.B.map d.q at hh
    rw [PointOffenders.row_conjugate a.toAdd ha] at hh
    exact hh

omit [Finite G] in
private theorem eq_of_sylowIn_of_two {A E : Subgroup G}
    (h : IsSylowSubgroupIn A E) (hp : IsPGroup 2 E) : A = E := by
  obtain ⟨S,hS⟩ := h
  have hs : (S : Subgroup E) = ⊤ := (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  change (S : Subgroup E).map E.subtype = A at hS
  simpa only [hs,← MonoidHom.range_eq_map,range_subtype] using hS.symm

theorem core_J_le_B (hne : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥) :
    pCore 2 d.J ≤ d.B.subgroupOf d.J := by
  have hs := (d.baumann_conclusions hne).2.2.1
  rw [← d.kernel_centralizer,d.kernel] at hs
  have he : d.B ⊓ pCore 2 G = d.J ⊓ pCore 2 G :=
    eq_of_sylowIn_of_two hs (pCore_isPGroup.to_le inf_le_right)
  intro x hx
  have hxQ : (x:G) ∈ pCore 2 G := by rw [d.core_J] at hx; exact hx
  exact (he.symm ▸ show (x:G) ∈ d.J ⊓ pCore 2 G from ⟨x.property,hxQ⟩).1

theorem radical_intersection (hne : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥) :
    d.R ⊓ d.J = d.B := by
  apply le_antisymm
  · intro r hr
    have hq : d.q r ∈ d.B.map d.q := d.B_image hne ▸ hr.1
    obtain ⟨b,hb,he⟩ := hq
    have hk : r*b⁻¹ ∈ pCore 2 G := by
      rw [← d.kernel]
      change d.q (r*b⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hj : r*b⁻¹ ∈ d.J := mul_mem hr.2 (inv_mem (mem_sup_right hb))
    have hc : (⟨r*b⁻¹,hj⟩ : d.J) ∈ pCore 2 d.J := by rw [d.core_J]; exact hk
    have hmem : r*b⁻¹ ∈ d.B := d.core_J_le_B hne hc
    simpa only [inv_mul_cancel_right] using d.B.mul_mem hmem hb
  · exact le_inf inf_le_left le_sup_right


private theorem root_displacement (i : Fin 3) :
    PointOffenders.root i • (Pi.single (i+1) (1 : ZMod 2) : Geometry.Vector) - Pi.single (i+1) 1 =
      Pi.single i 1 := by
  revert i
  decide +kernel

include d in
theorem module_le_commutator : V ≤ ⁅V,pResidual 2 G⁆ := by
  classical
  let W := AddSubgroup.toZModSubmodule 2 ((⁅V,pResidual 2 G⁆).comap V.subtype).toAddSubgroup
  have htop : W.map d.linearCoordinates.toLinearMap = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun (ZMod 2) (Fin 3))).mpr
    intro i
    obtain ⟨g,hg⟩ := d.residual_surjective (PointOffenders.root i)
    let v : V := d.coordinates.symm (Multiplicative.ofAdd (Pi.single (i+1) 1))
    let w : V := MulAut.conjNormal (g:G) v * v⁻¹
    have hw : (w:G) ∈ ⁅V,pResidual 2 G⁆ := by
      change ⁅(g:G),(v:G)⁆ ∈ ⁅V,pResidual 2 G⁆
      rw [commutator_comm]
      exact commutator_mem_commutator g.property v.property
    rw [Pi.basisFun_apply]
    change Pi.single i (1 : ZMod 2) ∈ W.map d.linearCoordinates.toLinearMap
    refine ⟨Additive.ofMul w,hw,?_⟩
    change (d.coordinates (MulAut.conjNormal (g:G) v * v⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [d.action,show d.q g = PointOffenders.root i from hg]
    dsimp only [v]
    rw [d.coordinates.apply_symm_apply]
    exact root_displacement i
  intro v hv
  have hm : d.linearCoordinates (Additive.ofMul (⟨v,hv⟩ : V)) ∈
      W.map d.linearCoordinates.toLinearMap := htop ▸ Submodule.mem_top
  obtain ⟨w,hw,he⟩ := hm
  have hwv : w = Additive.ofMul (⟨v,hv⟩ : V) := d.linearCoordinates.injective he
  rw [hwv] at hw
  exact hw

include d in
theorem module_commutator : ⁅V,pResidual 2 G⁆ = V :=
  le_antisymm (commutator_le_left _ _) d.module_le_commutator

include d in
theorem module_le_residual : V ≤ pResidual 2 G :=
  d.module_le_commutator.trans (commutator_le_right _ _)

theorem module_le_J : V ≤ d.J := d.module_le_residual.trans le_sup_left

theorem module_centralizer_J :
    centralizer (V.subgroupOf d.J : Set d.J) = pCore 2 d.J := by
  rw [d.core_J,← d.kernel, d.kernel_centralizer]
  ext j
  constructor
  · intro hj
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_centralizer_iff.mp hj
      (⟨v,d.module_le_J hv⟩ : d.J) hv)
  · intro hj
    apply mem_centralizer_iff.mpr
    intro v hv
    exact Subtype.ext (mem_centralizer_iff.mp hj (v:G) hv)

theorem fitting_J : generalizedFitting d.J = pCore 2 d.J := by
  have hVQ : V.subgroupOf d.J ≤ pCore 2 d.J := by
    rw [d.core_J,← d.kernel,d.kernel_centralizer]
    intro v hv
    exact V.le_centralizer hv
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  rw [← d.module_centralizer_J]
  exact centralizer_le (hVQ.trans_eq d.module_centralizer_J.symm)


noncomputable abbrev LJ : Subgroup d.J := (pResidual 2 G).subgroupOf d.J
noncomputable abbrev BJ : Subgroup d.J := d.B.subgroupOf d.J
noncomputable abbrev PJ : Subgroup d.J := d.P.subgroupOf d.J
noncomputable def qJ : d.J →* SL := d.q.comp d.J.subtype

omit [IsElementaryAbelian 2 V] in
theorem qJ_surjective : Function.Surjective d.qJ := by
  intro g
  obtain ⟨l,hl⟩ := d.residual_surjective g
  exact ⟨⟨l,mem_sup_left l.property⟩,hl⟩

omit [IsElementaryAbelian 2 V] in
theorem qJ_kernel : d.qJ.ker = pCore 2 d.J := by
  rw [d.core_J,← d.kernel]
  rfl

omit [IsElementaryAbelian 2 V] in
theorem PJ_index : d.PJ.index = 7 := by
  change (pointParabolicSL.comap d.qJ).index = 7
  rw [pointParabolicSL.index_comap_of_surjective d.qJ_surjective]
  have hc := pointParabolicSL.card_mul_index
  rw [card_pointParabolicSL,card_SL] at hc
  omega

theorem PJ_core (hne : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥) :
    d.PJ.pCoreIn 2 = d.BJ := by
  have hp : IsPGroup 2 d.qJ.ker := d.qJ_kernel.symm ▸ pCore_isPGroup
  have hPm : d.PJ.map d.qJ = pointParabolicSL := by
    change (pointParabolicSL.comap d.qJ).map d.qJ = _
    rw [map_comap_eq,MonoidHom.range_eq_top.mpr d.qJ_surjective,top_inf_eq]
  have hBm : d.BJ.map d.qJ = pointV := by
    rw [qJ,← map_map]
    rw [map_subgroupOf_eq_of_le (show d.B ≤ d.J from le_sup_right)]
    exact d.B_image hne
  have hm : (d.PJ.pCoreIn 2).map d.qJ = pointV := by
    rw [map_pCoreIn_of_ker_isPGroup d.qJ hp,hPm]
    exact Matrix.PSL3Two.MarkedProduct.pointParabolic_core
  have hk : d.qJ.ker ≤ d.PJ.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hp
    · intro j hj
      change d.qJ j ∈ pointParabolicSL
      rw [show d.qJ j = 1 from hj]
      exact one_mem _
    · rw [normalizer_eq_top]
      exact le_top
  have hBk : d.qJ.ker ≤ d.BJ := d.qJ_kernel ▸ d.core_J_le_B hne
  rw [← comap_map_eq_self hk,← comap_map_eq_self hBk,hm,hBm]

theorem odd_index_radical (hne : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥) :
    MSOddIndexRadical d.BJ := by
  refine ⟨d.PJ,?_,?_,d.PJ_core hne⟩
  · apply lt_top_iff_ne_top.mpr
    intro ht
    have hh := d.PJ_index
    rw [ht,index_top] at hh
    norm_num at hh
  · rw [d.PJ_index]
    decide

noncomputable def componentEquiv : (d.LJ ⧸ pCore 2 d.LJ) ≃* SL := by
  let q := d.qJ.comp d.LJ.subtype
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨l,hl⟩ := d.residual_surjective g
    exact ⟨⟨⟨l,mem_sup_left l.property⟩,l.property⟩,hl⟩
  have hk : q.ker = pCore 2 d.LJ := by
    have he := pCore_subnormal_eq_comap 2 (inferInstance : d.LJ.Normal).isSubnormal
    rw [he,← d.qJ_kernel]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)


private theorem characteristic_map_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (C : Subgroup H) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut H := e.trans (a.trans e.symm)
  refine ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,?_⟩
  exact e.apply_symm_apply _

omit [IsElementaryAbelian 2 V] in
theorem characteristic_condition
    (hno : ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) : MSCharacteristicCondition d.BJ := by
  intro C hC hne hn
  let e : d.BJ ≃* d.B := subgroupOfEquivOfLe (show d.B ≤ d.J from le_sup_right)
  let D := C.map e.toMonoidHom
  have hD : D.Characteristic := characteristic_map_equiv e C hC
  have hDne : D ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz)
  have he : D.map d.B.subtype = (C.map d.BJ.subtype).map d.J.subtype := by
    rw [map_map,map_map]
    rfl
  have hJN : d.J ≤ normalizer (D.map d.B.subtype : Set G) := by
    rw [he]
    have h := (C.map d.BJ.subtype).le_normalizer_map d.J.subtype
    let := hn
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h
  have hPN : d.P ≤ normalizer (D.map d.B.subtype : Set G) := by
    let := hD
    exact d.normalizes_B.trans (normalizer_le_normalizer_characteristic_image d.B D)
  have hnormal : (D.map d.B.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_iff.mpr
    rw [← d.residual_sup_P]
    exact sup_le (le_sup_left.trans hJN) hPN
  exact hno ⟨D,hD,hDne,hnormal⟩

noncomputable def msInput {κ : GroupClass}
    (hsqtk : IsSQTK κ G) (hcomp : (pResidual 2 G).IsCComponent)
    (hno : ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) : BinaryMS.Input κ d.LJ d.BJ where
  sqtk := hsqtk.subgroup d.J
  fitting := d.fitting_J
  product := by
    intro j
    obtain ⟨l,hl,b,hb,he⟩ := mem_sup_of_normal_left.mp j.property
    exact ⟨⟨l,mem_sup_left hl⟩,hl,⟨b,mem_sup_right hb⟩,hb,Subtype.ext he⟩
  component := hcomp.subgroupOf le_sup_left
  radical := d.odd_index_radical (fun hz => hno (d.characteristic_of_thompson_image_bot hz))
  characteristic := d.characteristic_condition hno
  quotientEquiv := d.componentEquiv

theorem characteristic_or_msInput {κ : GroupClass}
    (hsqtk : IsSQTK κ G) (hcomp : (pResidual 2 G).IsCComponent) :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ Nonempty (BinaryMS.Input κ d.LJ d.BJ) := by
  by_cases h : ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal
  · exact Or.inl h
  · exact Or.inr ⟨d.msInput hsqtk hcomp h⟩


omit [IsElementaryAbelian 2 V] in
/-- The MS quotient marking is the restriction of the original projection. -/
theorem componentEquiv_apply (l : d.LJ) :
    d.componentEquiv (QuotientGroup.mk' (pCore 2 d.LJ) l) = d.q (l.val.val) := rfl

/-- The original natural module lies in the literal MS commutator core.
This is the inclusion needed for the later doubled-module orientation test. -/
theorem module_le_MS_core : V.subgroupOf d.J ≤ BinaryMS.commutatorCore d.LJ := by
  have hV : (V.subgroupOf d.J).map d.J.subtype = V :=
    map_subgroupOf_eq_of_le d.module_le_J
  have hL : d.LJ.map d.J.subtype = pResidual 2 G :=
    map_subgroupOf_eq_of_le le_sup_left
  have hVQ : V ≤ (pCore 2 d.J).map d.J.subtype := by
    rw [d.core_J,map_comap_eq,range_subtype]
    apply le_inf d.module_le_J
    rw [← d.kernel,d.kernel_centralizer]
    exact V.le_centralizer
  apply (map_le_map_iff_of_injective (f := d.J.subtype) d.J.subtype_injective).mp
  rw [hV,BinaryMS.commutatorCore,map_commutator,hL]
  exact d.module_le_commutator.trans (commutator_mono hVQ le_rfl)

end NaturalAction

/-- The actual marked point source gives the literal MS pair in O²(G)Baum(O₂(P)),
or the genuine characteristic-normal-subgroup alternative. -/
theorem point_ms_source {κ : GroupClass}
    (hsqtk : IsSQTK κ G) (hcomp : (pResidual 2 G).IsCComponent)
    (e : (G ⧸ pCore 2 G) ≃* SL) (c : V ≃* Multiplicative Geometry.Vector)
    (ha : ∀ g v, (c (MulAut.conjNormal g v)).toAdd =
      e (QuotientGroup.mk' (pCore 2 G) g) • (c v).toAdd)
    (P : Subgroup G)
    (hP : pointParabolicSL.comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))) = P) :
    (∃ C : Subgroup (baumann (P.pCoreIn 2)), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (baumann (P.pCoreIn 2)).subtype).Normal) ∨
    Nonempty (BinaryMS.Input κ
      ((pResidual 2 G).subgroupOf (pResidual 2 G ⊔ baumann (P.pCoreIn 2)))
      ((baumann (P.pCoreIn 2)).subgroupOf (pResidual 2 G ⊔ baumann (P.pCoreIn 2)))) := by
  let d := ofQuotient V e c ha
  have he : d.P = P := hP
  have hR : d.R = P.pCoreIn 2 := d.R_eq_parabolic_core.trans (congrArg (fun P => P.pCoreIn 2) he)
  let conclusion (R : Subgroup G) : Prop :=
    (∃ C : Subgroup (baumann R), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (baumann R).subtype).Normal) ∨
    Nonempty (BinaryMS.Input κ
      ((pResidual 2 G).subgroupOf (pResidual 2 G ⊔ baumann R))
      ((baumann R).subgroupOf (pResidual 2 G ⊔ baumann R)))
  have hh : conclusion d.R := d.characteristic_or_msInput hsqtk hcomp
  exact (congrArg conclusion hR).mp hh

end CFSG.Quasithin.ChapterC.NaturalPointControl
