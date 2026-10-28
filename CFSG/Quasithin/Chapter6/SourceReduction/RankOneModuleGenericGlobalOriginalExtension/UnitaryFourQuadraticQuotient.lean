module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCoreCollapse
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PlaneOuter

/-!
# Identifying the original U₄ quadratic quotient

The proved exact field kernel and index-two bound determine the actual field
image: every original S-element outside L induces the unique quadratic
conjugation on the field of order q². Since L supplies every inner actor,
conjugation identifies LS/O₂(LS) with the concrete subgroup of Aut(PSL₂(q²))
whose field coefficients are the identity or this conjugation. The equivalence
retains every original representative and the literal L and S actions.

The native graph automorphism of the plane residual induces that same specified
quadratic action. Its preimage gives an actual element g of LS outside L with
g² in O₂(L), and an order-two quotient class. This does not assert that g is an
involution in G. Lifting the graph action through the core and constructing
both full-endpoint maps and the whole Borel comparison remain necessary.

All results retain arbitrary selected perfect R, both input orientations and
q=4. The Chapter 12 application also uses genuine reduced DGS restoration and
the completed ordinary prepared recognition. DGS exhaustion, uniqueness and
unconditional GlobalExit retain their original assembly obligations.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6--7, pp.650--651
(`refs/quasithin.pdf`). The private cyclic-field argument follows
`Theory/Representation/OrthogonalFourMinusRankOne/AmbientActions/Elementary.lean`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace OriginalUnitaryFour

private theorem field_square_cases (m : ℕ) (hm : 1 ≤ m)
    (σ : MatrixField m ≃+* MatrixField m) (hs : σ^2=1) :
    σ=1 ∨ σ=fieldConj m := by
  classical
  let : IsCyclic (MatrixField m ≃+* MatrixField m) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (MatrixField m ≃+* MatrixField m) := Finite.of_injective
    (fun e : MatrixField m ≃+* MatrixField m => (e : MatrixField m → MatrixField m)) DFunLike.coe_injective
  let := Fintype.ofFinite (MatrixField m ≃+* MatrixField m)
  have hconj2 : fieldConj m ^ 2 = 1 := by ext x; exact fieldConj_involutive m hm x
  have hconjne : fieldConj m ≠ 1 := by
    obtain ⟨x,hx⟩ := PointLocal.fieldConj_nontrivial m hm
    exact fun he => hx (DFunLike.congr_fun he x)
  by_contra! hne
  have hle : ({1,σ,fieldConj m} : Finset (MatrixField m ≃+* MatrixField m)) ⊆
      Finset.univ.filter (fun a => a^2=1) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hs,hconj2]
  have hc : ({1,σ,fieldConj m} : Finset (MatrixField m ≃+* MatrixField m)).card = 3 := by
    simp [hne.2,Ne.symm hne.1,Ne.symm hconjne]
  have hb := IsCyclic.card_pow_eq_one_le (α := MatrixField m ≃+* MatrixField m) (n := 2) (by decide)
  have hh := Finset.card_le_card hle
  rw [hc] at hh
  omega

/-- The canonical quadratic semilinear subgroup of the actual PSL₂ automorphism group. -/
@[expose] def quadraticQuotient (m : ℕ) : Subgroup (MulAut (Theory.PSL2.Group (MatrixField m))) :=
  (zpowers (fieldConj m)).comap (Theory.PSL2.fieldProjection (MatrixField m))

private theorem field_mem_quadratic_iff (m : ℕ) (hm : 1 ≤ m)
    (σ : MatrixField m ≃+* MatrixField m) :
    σ ∈ zpowers (fieldConj m) ↔ σ=1 ∨ σ=fieldConj m := by
  constructor
  · rintro ⟨k,rfl⟩
    apply field_square_cases m hm
    have h2 : fieldConj m ^ 2 = 1 := by ext x; exact fieldConj_involutive m hm x
    rw [←zpow_natCast,←_root_.zpow_mul,mul_comm k,_root_.zpow_mul,zpow_natCast,h2,_root_.one_zpow]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _


/-- PSL₂ coordinates on the literal plane residual quotient. -/
@[expose] def planeQuotient (m : ℕ) (hm : 1 ≤ m) :
    (L2 m hm ⧸ pCore 2 (L2 m hm)) ≃* Theory.PSL2.Group (MatrixField m) :=
  (Extension.L2QuotientEquivMatrixSL2 m hm).trans (Theory.PSL2.sl2QuotientEquiv (MatrixField m))

/-- The native graph actor has precisely the same quadratic coefficient. -/
theorem planeQuotient_graph (m : ℕ) (hm : 1 ≤ m) :
    MulAut.congr (planeQuotient m hm) (Extension.L2QuotientAut m hm) =
      Theory.PSL2.fieldAut (fieldConj m) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (planeQuotient m hm).surjective x
  change planeQuotient m hm (Extension.L2QuotientAut m hm ((planeQuotient m hm).symm
    (planeQuotient m hm y))) = _
  rw [MulEquiv.symm_apply_apply]
  change Theory.PSL2.sl2QuotientEquiv (MatrixField m)
    (Extension.L2QuotientEquivMatrixSL2 m hm (Extension.L2QuotientAut m hm y)) = _
  rw [Extension.L2QuotientAut_field]
  change _ = Theory.PSL2.sl2QuotientEquiv (MatrixField m)
    (Theory.PSL2.sl2FieldAut (fieldConj m) ((Theory.PSL2.sl2QuotientEquiv (MatrixField m)).symm
      (Theory.PSL2.sl2QuotientEquiv (MatrixField m) (Extension.L2QuotientEquivMatrixSL2 m hm y))))
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The specified graph involution in the quadratic quotient model. -/
@[expose] def quadraticGraph (m : ℕ) : quadraticQuotient m :=
  ⟨Theory.PSL2.fieldAut (fieldConj m),by
    change Theory.PSL2.fieldProjection (MatrixField m) _ ∈ zpowers (fieldConj m)
    rw [Theory.PSL2.fieldProjection_fieldAut]
    exact mem_zpowers _⟩

/-- This is an actual outer involution, including at q=4. -/
theorem quadraticGraph_order (m : ℕ) (hm : 1 ≤ m) : orderOf (quadraticGraph m)=2 := by
  rw [←Subgroup.orderOf_coe]
  change orderOf (Theory.PSL2.fieldAut (fieldConj m))=2
  rw [Theory.PSL2.orderOf_fieldAut]
  apply orderOf_eq_prime
  · ext x
    exact fieldConj_involutive m hm x
  · obtain ⟨x,hx⟩ := PointLocal.fieldConj_nontrivial m hm
    exact fun he => hx (DFunLike.congr_fun he x)

theorem quadraticGraph_not_inner (m : ℕ) (hm : 1 ≤ m) :
    (quadraticGraph m).val ∉ MulAut.innerSubgroup (Theory.PSL2.Group (MatrixField m)) := by
  intro hc
  have hh : Theory.PSL2.fieldProjection (MatrixField m) (quadraticGraph m).val=1 := by
    apply MonoidHom.mem_ker.mp
    rw [Theory.PSL2.fieldProjection_ker]
    exact hc
  rw [quadraticGraph,Theory.PSL2.fieldProjection_fieldAut] at hh
  obtain ⟨x,hx⟩ := PointLocal.fieldConj_nontrivial m hm
  exact hx (DFunLike.congr_fun hh x)

end OriginalUnitaryFour
namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
  (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m))
include d hp mark

/-- The coefficient is the identity exactly on the original inner Sylow. -/
theorem original_unitaryFour_field_eq_one_iff (s : sourceS L H) :
    originalUnitaryFourLeftFieldAction h hTH q s=1 ↔ s.val ∈ L := by
  change s ∈ (originalUnitaryFourLeftFieldAction h hTH q).ker ↔ _
  rw [d.original_unitaryFour_left_field_kernel_exact h hTH hp m hm point mark q]
  rfl

/-- Every element outside L has the specified quadratic field coefficient. -/
theorem original_unitaryFour_field_eq_conjugation (s : sourceS L H) (hs : s.val ∉ L) :
    originalUnitaryFourLeftFieldAction h hTH q s=fieldConj m := by
  exact (OriginalUnitaryFour.field_square_cases m hm _
    (d.original_unitaryFour_left_field_square h hTH hp m hm point mark q s)).resolve_left
      (fun he => hs ((d.original_unitaryFour_field_eq_one_iff h hTH hp m hm point mark q s).mp he))

/-- The exact nontrivial original field image is generated by quadratic conjugation. -/
theorem original_unitaryFour_field_range
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    (originalUnitaryFourLeftFieldAction h hTH q).range = zpowers (fieldConj m) := by
  apply le_antisymm
  · rintro _ ⟨s,rfl⟩
    exact (OriginalUnitaryFour.field_mem_quadratic_iff m hm _).mpr
      (OriginalUnitaryFour.field_square_cases m hm _
        (d.original_unitaryFour_left_field_square h hTH hp m hm point mark q s))
  · apply zpowers_le.mpr
    have hnot : ¬ sourceS L H ≤ L := by
      intro hs
      have hle := le_inf (sourceS_le_sylow h.sylow_normalizes hTH) hs
      have he := relIndex_eq_one.mpr hle
      omega
    obtain ⟨s,hs,hsL⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨⟨s,hs⟩,d.original_unitaryFour_field_eq_conjugation h hTH hp m hm point mark q ⟨s,hs⟩ hsL⟩

/-- Actual conjugation of LS on the marked left quotient. -/
@[expose] def originalUnitaryFourJoinAction : (L ⊔ sourceS L H : Subgroup G) →*
    MulAut (Theory.PSL2.Group (MatrixField m)) :=
  (MulAut.congr q).toMonoidHom.comp
    (pCoreJoinAction 2 ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes))

omit d hp hm point mark in
/-- The full join action restricts to the unchanged original S action. -/
theorem originalUnitaryFourJoinAction_field (s : sourceS L H) :
    Theory.PSL2.fieldProjection (MatrixField m)
      (originalUnitaryFourJoinAction h hTH m q (inclusion le_sup_right s)) =
        originalUnitaryFourLeftFieldAction h hTH q s := rfl

omit d hp hm point mark in
/-- The selected L acts by its literal inner conjugation. -/
theorem originalUnitaryFourJoinAction_left (l : L) :
    originalUnitaryFourJoinAction h hTH m q (inclusion le_sup_left l) =
      MulAut.conj (q (QuotientGroup.mk' (pCore 2 L) l)) := by
  change (MulAut.congr q) (pCoreJoinAction 2 _ _) = _
  rw [pCoreJoinAction_on_component,MulAut.congr_conj]

omit d hp hm point mark in
private theorem join_inner_le :
    MulAut.innerSubgroup (Theory.PSL2.Group (MatrixField m)) ≤
      (originalUnitaryFourJoinAction h hTH m q).range := by
  rintro _ ⟨g,rfl⟩
  obtain ⟨l,rfl⟩ := q.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  exact ⟨inclusion le_sup_left l,originalUnitaryFourJoinAction_left h hTH m q l⟩

omit d hp hm point mark in
private theorem join_field_range :
    ((Theory.PSL2.fieldProjection (MatrixField m)).comp
      (originalUnitaryFourJoinAction h hTH m q)).range =
        (originalUnitaryFourLeftFieldAction h hTH q).range := by
  let M := L ⊔ sourceS L H
  let a := originalUnitaryFourJoinAction h hTH m q
  let f := (Theory.PSL2.fieldProjection (MatrixField m)).comp a
  let I := (originalUnitaryFourLeftFieldAction h hTH q).range
  let K := (I.comap f).map M.subtype
  have hLK : L ≤ K := by
    intro x hx
    refine ⟨inclusion le_sup_left (⟨x,hx⟩ : L),?_,rfl⟩
    change Theory.PSL2.fieldProjection (MatrixField m) (a (inclusion le_sup_left _)) ∈ I
    rw [originalUnitaryFourJoinAction_left]
    have he : Theory.PSL2.fieldProjection (MatrixField m)
        (MulAut.conj (q (QuotientGroup.mk' (pCore 2 L) ⟨x,hx⟩)))=1 := by
      apply MonoidHom.mem_ker.mp
      rw [Theory.PSL2.fieldProjection_ker]
      exact ⟨_,rfl⟩
    rw [he]
    exact I.one_mem
  have hSK : sourceS L H ≤ K := by
    intro x hx
    refine ⟨inclusion le_sup_right (⟨x,hx⟩ : sourceS L H),?_,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact (mem_map_iff_mem M.subtype_injective).mp ((sup_le hLK hSK) x.property)
  · rintro _ ⟨s,rfl⟩
    exact ⟨inclusion le_sup_right s,rfl⟩

/-- The full actual left quotient action is exactly inner-quadratic semilinear. -/
theorem original_unitaryFour_join_action_range
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    (originalUnitaryFourJoinAction h hTH m q).range = OriginalUnitaryFour.quadraticQuotient m := by
  have he := join_field_range h hTH m q
  rw [d.original_unitaryFour_field_range h hTH hp m hm point mark q hi,
    MonoidHom.range_comp] at he
  have hk : (Theory.PSL2.fieldProjection (MatrixField m)).ker ≤
      (originalUnitaryFourJoinAction h hTH m q).range := by
    rw [Theory.PSL2.fieldProjection_ker]
    exact join_inner_le h hTH m q
  exact (comap_map_eq_self hk).symm.trans (congrArg (fun J => J.comap
    (Theory.PSL2.fieldProjection (MatrixField m))) he)

omit d hp hm point mark in
/-- The full left quotient is detected faithfully by its actual conjugation action. -/
theorem originalUnitaryFourJoinAction_kernel :
    (originalUnitaryFourJoinAction h hTH m q).ker = pCore 2 (L ⊔ sourceS L H : Subgroup G) := by
  rw [originalUnitaryFourJoinAction,MonoidHom.ker_comp_of_injective _ _ (MulAut.congr q).injective]
  apply pCoreJoinAction_kernel 2 _ (pCore_isPGroup.map _)
  apply map_injective (f := q.toMonoidHom) q.injective
  rw [center_map_equiv,Subgroup.map_bot]
  apply bot_unique
  intro x hx
  apply Theory.PSL2.psl2_conj_eq_one_implies x
  ext y
  change x*y*x⁻¹=y
  rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]

/-- The original LS quotient is the literal quadratic semilinear group,
with no extension recognition or graph-lifting hypothesis. -/
def originalUnitaryFourQuadraticQuotientEquiv
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ((L ⊔ sourceS L H : Subgroup G) ⧸ pCore 2 (L ⊔ sourceS L H : Subgroup G)) ≃*
      OriginalUnitaryFour.quadraticQuotient m :=
  (QuotientGroup.quotientMulEquivOfEq (originalUnitaryFourJoinAction_kernel h hTH m q).symm).trans
    ((QuotientGroup.quotientKerEquivRange (originalUnitaryFourJoinAction h hTH m q)).trans
      (MulEquiv.subgroupCongr (d.original_unitaryFour_join_action_range h hTH hp m hm point mark q hi)))

/-- The quotient equivalence retains every actual original representative. -/
theorem originalUnitaryFourQuadraticQuotientEquiv_mk
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (x : (L ⊔ sourceS L H : Subgroup G)) :
    (d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi
      (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) x)).val =
        originalUnitaryFourJoinAction h hTH m q x := by rfl

/-- The same equivalence identifies the original L image with literal inner action. -/
theorem originalUnitaryFourQuadraticQuotientEquiv_left
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) (l : L) :
    (d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi
      (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G))
        (inclusion le_sup_left l))).val = MulAut.conj (q (QuotientGroup.mk' (pCore 2 L) l)) := by
  rw [originalUnitaryFourQuadraticQuotientEquiv_mk]
  exact originalUnitaryFourJoinAction_left h hTH m q l

/-- The original S parity is exactly membership in L, with canonical graph coefficient outside. -/
theorem originalUnitaryFourQuadraticQuotientEquiv_outer
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (s : sourceS L H) (hs : s.val ∉ L) :
    Theory.PSL2.fieldProjection (MatrixField m)
      (d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi
        (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G))
          (inclusion le_sup_right s))).val = fieldConj m := by
  rw [originalUnitaryFourQuadraticQuotientEquiv_mk]
  exact d.original_unitaryFour_field_eq_conjugation h hTH hp m hm point mark q s hs

/-- A source quotient representative of the specified native graph actor.
Its square lies in the proved original core; it is not asserted to be
an involution of G before the remaining lift calculation is supplied. -/
theorem original_unitaryFour_graph_quotient_lift
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ g : (L ⊔ sourceS L H : Subgroup G), g.val ∉ L ∧
      g.val^2 ∈ L.pCoreIn 2 ∧
      originalUnitaryFourJoinAction h hTH m q g =
        MulAut.congr (OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) ∧
      orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) g)=2 := by
  let M := L ⊔ sourceS L H
  let e := d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi
  let z := e.symm (OriginalUnitaryFour.quadraticGraph m)
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 M) z
  have he : e (QuotientGroup.mk' (pCore 2 M) g) = OriginalUnitaryFour.quadraticGraph m := by
    rw [hg]
    exact e.apply_symm_apply _
  have hact : originalUnitaryFourJoinAction h hTH m q g =
      (OriginalUnitaryFour.quadraticGraph m).val := congrArg Subtype.val he
  have horder : orderOf (QuotientGroup.mk' (pCore 2 M) g)=2 := by
    calc
      _ = orderOf (e (QuotientGroup.mk' (pCore 2 M) g)) :=
        (orderOf_injective e.toMonoidHom e.injective _).symm
      _ = 2 := by rw [he]; exact OriginalUnitaryFour.quadraticGraph_order m hm
  have hnot : g.val ∉ L := by
    intro hgL
    have hl := originalUnitaryFourJoinAction_left h hTH m q (⟨g.val,hgL⟩ : L)
    change originalUnitaryFourJoinAction h hTH m q g = _ at hl
    exact OriginalUnitaryFour.quadraticGraph_not_inner m hm ⟨_,hl.symm.trans hact⟩
  have hsq : g^2 ∈ pCore 2 M := by
    apply (QuotientGroup.eq_one_iff (g^2)).mp
    change QuotientGroup.mk' (pCore 2 M) (g^2)=1
    rw [map_pow]
    have hh := pow_orderOf_eq_one (QuotientGroup.mk' (pCore 2 M) g)
    rwa [horder] at hh
  have hsqG : g.val^2 ∈ M.pCoreIn 2 := mem_map_of_mem M.subtype hsq
  rw [d.original_unitaryFour_left_core_eq h hTH hp m hm point mark] at hsqG
  refine ⟨g,hnot,hsqG,?_,horder⟩
  rw [OriginalUnitaryFour.planeQuotient_graph]
  exact hact

/-- Coordinates supplied by the actual original residual identification. -/
def originalUnitaryFourQuotientCoordinates :
    (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m) :=
  let a := (d.original_unitaryFour_factors h hTH hp m hm point mark).2.1.some
  (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (OriginalUnitaryFour.planeQuotient m hm)

omit q in
/-- The degree-two branch gives its concrete quotient and a native graph
representative under only the broad original marking and exact index. -/
theorem original_unitaryFour_quadratic_quotient
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m),
    ∃ e : ((L ⊔ sourceS L H : Subgroup G) ⧸ pCore 2 (L ⊔ sourceS L H : Subgroup G)) ≃*
      OriginalUnitaryFour.quadraticQuotient m,
      (∀ x, (e (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) x)).val =
        originalUnitaryFourJoinAction h hTH m q x) ∧
      ∃ g : (L ⊔ sourceS L H : Subgroup G), g.val ∉ L ∧ g.val^2 ∈ L.pCoreIn 2 ∧
        originalUnitaryFourJoinAction h hTH m q g =
          MulAut.congr (OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) ∧
        orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ sourceS L H : Subgroup G)) g)=2 := by
  let q := d.originalUnitaryFourQuotientCoordinates h hTH hp m hm point mark
  exact ⟨q,d.originalUnitaryFourQuadraticQuotientEquiv h hTH hp m hm point mark q hi,
    d.originalUnitaryFourQuadraticQuotientEquiv_mk h hTH hp m hm point mark q hi,
    d.original_unitaryFour_graph_quotient_lift h hTH hp m hm point mark q hi⟩

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
