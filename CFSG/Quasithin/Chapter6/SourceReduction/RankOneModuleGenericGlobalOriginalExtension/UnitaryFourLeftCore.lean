module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourFieldDegree
public import Theory.Representation.OrthogonalFourMinusBinaryIrreducibility
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.Representation.FirstCohomologyAutomorphism
public import Theory.Representation.OrthogonalFourMinusFirstCohomology

/-!
# The exact original U₄ action kernel

The marked plane core is irreducible under the selected L. Consequently
O₂(LS) centralizes it. Characteristic two in L and the centerless quotient
identify this centralizer, inside either LS or S, with the entire join-core.
This gives the exact kernel of the literal S action on the Hermitian core.

Vanishing Hermitian H¹ corrects each join-core actor by an element of O₂(L),
leaving an element of C_S(L). Thus O₂(LS)=O₂(L) C_S(L), with trivial
intersection. The full outer index is |C_S(L)| or 2|C_S(L)|, and the right
join-core has the corresponding q⁵ multiple. The same original endpoint
and whole-overlap marking make C_S(L) fix the entire native left residual.

All statements retain arbitrary selected perfect R, both input orientations
and q=4. They do not identify S with T or R with O²(H). The remaining native
pointwise-centralizer restriction must eliminate C_S(L); the original full
comparison, DGS exhaustion, uniqueness and GlobalExit are still required.
The companion Chapter 12 module includes the actual reduced-row restoration.

The irreducibility transport adapts `UnitarySource/FieldTransfer.lean` to
the original broad marking. Source: Aschbacher--Smith F.1.12, pp.263--264;
I.1.6(3), p.408 (Hermitian H¹); 5.2.6--7, pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark
/-- Every original L-invariant subgroup of its Hermitian two-core is trivial or the whole core. -/
theorem original_unitaryFour_core_irreducible
    (E : Subgroup G) (hEQ : E ≤ L.pCoreIn 2)
    (hLE : L ≤ normalizer (E : Set G)) : E = ⊥ ∨ E = L.pCoreIn 2 := by
  let : NeZero m := ⟨by omega⟩
  let Q := L.pCoreIn 2
  obtain ⟨e,f,hf⟩ := d.original_unitaryFour_hermitian_model h hTH hp m hm point mark
  let B := (E.subgroupOf Q).map f.toMonoidHom
  have hb : ∀ g x, x ∈ B → multiplicativeAction m g x ∈ B := by
    rintro g _ ⟨v,hv,rfl⟩
    obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    let w := f.symm (multiplicativeAction m g (f v))
    have hw : w.val = (l : G)*v.val*(l : G)⁻¹ := by
      have hh := hf l v
      change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
      rw [hl] at hh
      exact hh
    refine ⟨w,?_,f.apply_symm_apply _⟩
    change w.val ∈ E
    rw [hw]
    exact (mem_normalizer_iff.mp (hLE l.property) v.val).mp hv
  rcases multiplicativeAction_irreducible m B hb with he | he
  · left
    apply E.eq_bot_iff_forall.mpr
    intro x hx
    have hm : f ⟨x,hEQ hx⟩ ∈ B := mem_map_of_mem f.toMonoidHom hx
    rw [he,mem_bot] at hm
    exact congrArg Subtype.val (f.injective (hm.trans f.map_one.symm))
  · right
    apply le_antisymm hEQ
    intro x hx
    have hm : f ⟨x,hx⟩ ∈ B := he ▸ mem_top _
    obtain ⟨v,hv,hvx⟩ := hm
    have heq : v.val = x := congrArg Subtype.val (f.injective hvx)
    exact heq ▸ (show v.val ∈ E from hv)


/-- The original left join core centralizes the entire Hermitian core. -/
theorem original_unitaryFour_left_core_centralizes :
    (L ⊔ sourceS L H).pCoreIn 2 ≤ centralizer (L.pCoreIn 2 : Set G) := by
  have hn : L ⊔ sourceS L H ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)
  exact pCoreIn_le_centralizer_of_irreducible (L.pCoreIn 2) L
    (L ⊔ sourceS L H) (isPGroup_pCoreIn 2 L)
    ((pCoreIn_le 2 L).trans le_sup_left)
    (hn.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) le_sup_left
    (d.original_unitaryFour_core_irreducible h hTH hp m hm point mark)

omit hp m hm point mark in
include d h hTH in
/-- The original left core lies in S by its own relative Sylow placement. -/
theorem original_left_core_le_sourceS : (L ⊔ sourceS L H).pCoreIn 2 ≤ sourceS L H := by
  have hs : Chapter1.IsSylowIn 2 (sourceS L H)
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :=
    (d.hypothesisF11 h hTH).sylow_parabolic 0
  obtain ⟨Q,hQ⟩ := hs.restrict (show sourceS L H ≤ L ⊔ sourceS L H from le_sup_right)
    (show L ⊔ sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from le_sup_left)
  exact (Subgroup.map_mono (f := (L ⊔ sourceS L H).subtype)
    (pCore_isPGroup (p := 2) (G := (L ⊔ sourceS L H : Subgroup G))
      |>.le_sylow_of_normal Q)).trans hQ.le


omit d hp m hm point mark in
include h hTH in
private theorem left_core_centralizer_le :
    (L ⊔ sourceS L H) ⊓ centralizer (L.pCoreIn 2 : Set G) ≤
      (L ⊔ sourceS L H).pCoreIn 2 := by
  let Q := L.pCoreIn 2
  let J := L ⊔ sourceS L H
  have hn : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  let f := pCoreJoinAction 2 hn
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    obtain ⟨F,_,_,hF,⟨q⟩⟩ := h.linear
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply map_injective (f := q.toMonoidHom) q.injective
    rw [center_map_equiv,Subgroup.map_bot]
    apply bot_unique
    intro x hx
    apply Theory.PSL2.psl2_conj_eq_one_implies x
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]
  have hk : f.ker=pCore 2 J := pCoreJoinAction_kernel 2 hn (pCore_isPGroup.map _) hz
  have hself : L ⊓ centralizer (Q : Set G) ≤ Q :=
    (inf_centralizer_pCoreIn_le_iff 2 L).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.local_mem.2.2.2.1)
  have hLC : L ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))).trans
      (normalizer_le_normalizer_centralizer Q)
  intro x hx
  let g : J := ⟨x,hx.1⟩
  have hg : g ∈ f.ker := by
    apply MulEquiv.ext
    intro z
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    rw [pCoreJoinAction_mk]
    let b := L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hn) g) l
    have hval : b.val=x*l.val*x⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hb : b/l ∈ pCore 2 L := by
      apply (mem_map_iff_mem L.subtype_injective).mp
      apply hself
      refine ⟨(b/l).property,?_⟩
      have hh := (mem_normalizer_iff.mp (hLC l.property) x⁻¹).mp
        ((centralizer (Q : Set G)).inv_mem hx.2)
      have hc := (centralizer (Q : Set G)).mul_mem hx.2 hh
      change b.val / l.val ∈ centralizer (Q : Set G)
      rw [div_eq_mul_inv]
      rw [hval]
      simpa only [mul_assoc] using hc
    exact QuotientGroup.eq_iff_div_mem.mpr hb
  exact mem_map_of_mem J.subtype (hk ▸ hg)

/-- The enlarged left core is exactly the centralizer of the Hermitian
core in the original left join. -/
theorem original_unitaryFour_left_core_eq_centralizer :
    (L ⊔ sourceS L H).pCoreIn 2 =
      (L ⊔ sourceS L H) ⊓ centralizer (L.pCoreIn 2 : Set G) := by
  exact le_antisymm (le_inf (pCoreIn_le 2 _)
    (d.original_unitaryFour_left_core_centralizes h hTH hp m hm point mark))
    (left_core_centralizer_le h hTH)

/-- Restriction to the literal S retains all of the left core. -/
theorem original_unitaryFour_source_core_centralizer :
    sourceS L H ⊓ centralizer (L.pCoreIn 2 : Set G) = (L ⊔ sourceS L H).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf le_sup_right le_rfl).trans (left_core_centralizer_le h hTH)
  · exact le_inf (d.original_left_core_le_sourceS h hTH)
      (d.original_unitaryFour_left_core_centralizes h hTH hp m hm point mark)

/-- Conjugation by the literal original S on the embedded Hermitian core. -/
@[expose] def originalUnitaryFourCoreAction : sourceS L H →* MulAut (L.pCoreIn 2) :=
  (L.pCoreIn 2).normalizerMonoidHom.comp (inclusion
    (((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))

/-- The kernel on the full original core is the entire left join-core. -/
theorem original_unitaryFour_core_action_kernel :
    (originalUnitaryFourCoreAction h hTH).ker =
      ((L ⊔ sourceS L H).pCoreIn 2).subgroupOf (sourceS L H) := by
  rw [originalUnitaryFourCoreAction,←MonoidHom.comap_ker,
    normalizerMonoidHom_ker]
  have hh := d.original_unitaryFour_source_core_centralizer h hTH hp m hm point mark
  ext x
  change x.val ∈ centralizer (L.pCoreIn 2 : Set G) ↔ x.val ∈ (L ⊔ sourceS L H).pCoreIn 2
  exact ⟨fun hx => hh.le ⟨x.property,hx⟩,fun hx => (hh.ge hx).2⟩

omit d hp m hm point mark in
include h hTH in
/-- The left core meets the unchanged native Sylow in exactly O₂(L). -/
theorem original_left_core_intersection :
    ((T : Subgroup G) ⊓ L) ⊓ (L ⊔ sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf inf_le_right le_rfl).trans (inf_pCoreIn_le_of_le 2 le_sup_left)
  · obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
    have hQS : L.pCoreIn 2 ≤ (T : Subgroup G) ⊓ L := (pCoreIn_le_sylow L P).trans_eq hP
    exact le_inf hQS (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)))

omit hp m hm point mark in
include d h hTH in
private theorem left_field_kernel_product :
    (L ⊔ (L ⊔ sourceS L H).pCoreIn 2) ⊓ sourceS L H =
      (L ⊔ sourceS L H).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ L) := by
  let E := (L ⊔ sourceS L H).pCoreIn 2
  have hES := d.original_left_core_le_sourceS h hTH
  have hLE : L ≤ normalizer (E : Set G) :=
    (le_sup_left.trans (L ⊔ sourceS L H).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ sourceS L H) (pCore 2 (L ⊔ sourceS L H : Subgroup G)))
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (L : Set G) * (E : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right L E hLE]
      exact hx.1
    obtain ⟨l,hl,e,he,rfl⟩ := hx'
    have hlS : l ∈ sourceS L H := by
      have hh := (sourceS L H).mul_mem hx.2 ((sourceS L H).inv_mem (hES he))
      simpa only [mul_inv_cancel_right] using hh
    have hlT : l ∈ (T : Subgroup G) ⊓ L := d.left_intersection.le ⟨hlS,hl⟩
    exact (E ⊔ ((T : Subgroup G) ⊓ L)).mul_mem (mem_sup_right hlT) (mem_sup_left he)
  · exact sup_le (le_inf le_sup_right hES)
      (le_inf (inf_le_right.trans le_sup_left) (d.left_intersection.symm ▸ inf_le_left))

omit hp m hm point mark in
include d h hTH in
/-- The full outer Sylow index factors as the genuine left-core enlargement
times the field-image order. Neither factor is silently discarded. -/
theorem original_unitaryFour_outer_index_factorization
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
      (L.pCoreIn 2).relIndex ((L ⊔ sourceS L H).pCoreIn 2) *
        Nat.card (originalUnitaryFourLeftFieldAction h hTH q).range := by
  let E := (L ⊔ sourceS L H).pCoreIn 2
  let S₀ := (T : Subgroup G) ⊓ L
  have hES := d.original_left_core_le_sourceS h hTH
  have hS₀ : S₀ ≤ sourceS L H := d.left_intersection.symm.le.trans inf_le_left
  have hn : S₀ ≤ normalizer (E : Set G) :=
    ((hS₀.trans le_sup_right).trans (L ⊔ sourceS L H).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ sourceS L H) (pCore 2 (L ⊔ sourceS L H : Subgroup G)))
  have hfirst : S₀.relIndex (E ⊔ S₀) = (L.pCoreIn 2).relIndex E := by
    rw [relIndex_sup_of_normalizes _ _ hn,←inf_relIndex_right]
    rw [original_left_core_intersection h hTH]
  have hsecond : (E ⊔ S₀).relIndex (sourceS L H) =
      Nat.card (originalUnitaryFourLeftFieldAction h hTH q).range := by
    rw [←left_field_kernel_product d h hTH,inf_relIndex_right]
    change ((L ⊔ E).subgroupOf (sourceS L H)).index = _
    rw [←original_unitaryFour_left_field_kernel h hTH q,index_ker]
  exact ((relIndex_mul_relIndex S₀ (E ⊔ S₀) (sourceS L H)
    le_sup_right (sup_le hES hS₀)).symm).trans (by rw [hfirst,hsecond])

/-- The field factor is one or two, so these are the exact two remaining
possibilities for the full outer index before removing the action kernel. -/
theorem original_unitaryFour_outer_index_alternatives :
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
        (L.pCoreIn 2).relIndex ((L ⊔ sourceS L H).pCoreIn 2) ∨
      ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
        2 * (L.pCoreIn 2).relIndex ((L ⊔ sourceS L H).pCoreIn 2) := by
  obtain ⟨F,_,_,hF,⟨q⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := d.original_unitaryFour_left_field_card_le_two h hTH hp m hm point mark q
  let : Finite (originalUnitaryFourLeftFieldAction h hTH q).range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hpos := Nat.card_pos (α := (originalUnitaryFourLeftFieldAction h hTH q).range)
  have he := d.original_unitaryFour_outer_index_factorization h hTH q
  have hcases : Nat.card (originalUnitaryFourLeftFieldAction h hTH q).range = 1 ∨
      Nat.card (originalUnitaryFourLeftFieldAction h hTH q).range = 2 := by omega
  rcases hcases with hc | hc
  · exact Or.inl (by simpa only [hc,mul_one] using he)
  · exact Or.inr (by simpa only [hc,mul_comm] using he)
/-- Vanishing Hermitian H¹ corrects every enlarged-core actor by an
actual element of O₂(L), leaving an actor centralizing the whole L. -/
theorem original_unitaryFour_left_core_inner_correction
    (u : sourceS L H) (hu : u.val ∈ (L ⊔ sourceS L H).pCoreIn 2) :
    ∃ v ∈ L.pCoreIn 2, v*u.val ∈ centralizer (L : Set G) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.original_unitaryFour_hermitian_model h hTH hp m hm point mark
  let Q := L.pCoreIn 2
  let ei : pCore 2 L ≃* Q := (pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
  let c := ei.trans f
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker=pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hei (x : Q) : ((ei.symm x : pCore 2 L) : G)=x.val :=
    congrArg Subtype.val (ei.apply_symm_apply x)
  have he (g : L) (v : Space m) :
      (c.symm (Multiplicative.ofAdd (action m (q g) v)) : L) =
        g*(c.symm (Multiplicative.ofAdd v) : L)*g⁻¹ := by
    apply Subtype.ext
    change ((ei.symm (f.symm (Multiplicative.ofAdd (action m (q g) v))) : pCore 2 L) : G) =
      g.val*((ei.symm (f.symm (Multiplicative.ofAdd v)) : pCore 2 L) : G)*g.val⁻¹
    rw [hei,hei]
    have hh := hf g (f.symm (Multiplicative.ofAdd v))
    rw [f.apply_symm_apply] at hh
    exact hh
  have hn : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  let a := L.normalizerMonoidHom (inclusion hn u)
  have hau : quotientAut (pCore 2 L) a = 1 := by
    let J := L ⊔ sourceS L H
    have hju : inclusion le_sup_right u ∈ pCore 2 J :=
      (mem_map_iff_mem J.subtype_injective).mp hu
    exact pCore_le_pCoreJoinAction_kernel 2 hn hju
  have ha (g : L) : q (a g)=q g := by
    have hh := DFunLike.congr_fun hau (QuotientGroup.mk' (pCore 2 L) g)
    rw [quotientAut_apply_mk] at hh
    exact congrArg e hh
  have hfix (g : L) (hg : g ∈ pCore 2 L) : a g=g := by
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp
      (d.original_unitaryFour_left_core_centralizes h hTH hp m hm point mark hu)
        g.val (mem_map_of_mem L.subtype hg)).symm)
  let : Subsingleton (Representation.OneCohomology.H1 (action m)) :=
    action_H1_subsingleton m
  obtain ⟨v,hv⟩ := Representation.OneCohomology.automorphism_inner_of_H1_zero
    (pCore 2 L) q hq hker c (action m) he a ha hfix
  refine ⟨(v.val : G),mem_map_of_mem L.subtype v.property,mem_centralizer_iff.mpr ?_⟩
  intro g hg
  have hh := congrArg Subtype.val (hv (⟨g,hg⟩ : L))
  change (a (⟨g,hg⟩ : L)).val = (v.val : G)⁻¹*g*(v.val : G) at hh
  rw [normalizerMonoidHom_apply_apply_coe] at hh
  change u.val*g*u.val⁻¹=(v.val : G)⁻¹*g*(v.val : G) at hh
  change g*((v.val : G)*u.val)=((v.val : G)*u.val)*g
  calc
    g*((v.val : G)*u.val) = (v.val : G)*((v.val : G)⁻¹*g*(v.val : G))*u.val := by group
    _ = (v.val : G)*(u.val*g*u.val⁻¹)*u.val := by rw [hh]
    _ = ((v.val : G)*u.val)*g := by group

/-- The enlargement is precisely the residual centralizer factor. The
correction comes from the actual Hermitian cocycle, not a splitting premise. -/
theorem original_unitaryFour_left_core_factorization :
    (L ⊔ sourceS L H).pCoreIn 2 =
      L.pCoreIn 2 ⊔ (sourceS L H ⊓ centralizer (L : Set G)) := by
  have hn : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  have hQE : L.pCoreIn 2 ≤ (L ⊔ sourceS L H).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hn)
  have hES := d.original_left_core_le_sourceS h hTH
  apply le_antisymm
  · intro u hu
    obtain ⟨v,hv,hvc⟩ := d.original_unitaryFour_left_core_inner_correction
      h hTH hp m hm point mark ⟨u,hES hu⟩ hu
    have hvs : v*u ∈ sourceS L H := (sourceS L H).mul_mem (hES (hQE hv)) (hES hu)
    have hh := mul_mem_sup ((L.pCoreIn 2).inv_mem hv) (show v*u ∈ sourceS L H ⊓ centralizer (L : Set G) from ⟨hvs,hvc⟩)
    simpa only [inv_mul_cancel_left] using hh
  · apply sup_le hQE
    rw [←d.original_unitaryFour_source_core_centralizer h hTH hp m hm point mark]
    exact inf_le_inf le_rfl (centralizer_le (pCoreIn_le 2 L))

/-- No nonidentity element of the Hermitian core centralizes the whole
selected left factor. Thus the correction factor has trivial intersection. -/
theorem original_unitaryFour_core_disjoint_centralizer :
    Disjoint (L.pCoreIn 2) (sourceS L H ⊓ centralizer (L : Set G)) := by
  obtain ⟨_,⟨a⟩,_,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point mark
  have hc : pCore 2 L ⊓ center L = ⊥ := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_inf _ _ _ a.injective,pCore_map_iso,center_map_equiv,Subgroup.map_bot]
    exact L2TwoCore_inf_center m hm
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hx,hxc⟩
  obtain ⟨v,hv,rfl⟩ := hx
  have hvz : v ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hxc.2 l.val l.property)
  have hh : v ∈ (⊥ : Subgroup L) := hc ▸ (show v ∈ pCore 2 L ⊓ center L from ⟨hv,hvz⟩)
  exact congrArg Subtype.val (show v=1 from hh)
/-- The entire unresolved core enlargement has the order of the actual
S-centralizer of L; the product has trivial intersection. -/
theorem original_unitaryFour_left_core_index :
    (L.pCoreIn 2).relIndex ((L ⊔ sourceS L H).pCoreIn 2) =
      Nat.card (sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) := by
  let C := sourceS L H ⊓ centralizer (L : Set G)
  have hn : L.pCoreIn 2 ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (inf_le_right.trans
      (centralizer_le (pCoreIn_le 2 L)))).trans (Subgroup.centralizer_le_normalizer _)
  rw [d.original_unitaryFour_left_core_factorization h hTH hp m hm point mark,
    sup_comm,relIndex_sup_of_normalizes _ _ hn,←inf_relIndex_right,
    (d.original_unitaryFour_core_disjoint_centralizer h hTH hp m hm point mark).eq_bot,
    relIndex_bot_left]

/-- A literal numerical restriction on the full original S: its outer
index is the residual-centralizer order or twice that order. -/
theorem original_unitaryFour_outer_centralizer_alternatives :
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
        Nat.card (sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) ∨
      ((T : Subgroup G) ⊓ L).relIndex (sourceS L H) =
        2 * Nat.card (sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) := by
  simpa only [d.original_unitaryFour_left_core_index h hTH hp m hm point mark] using
    d.original_unitaryFour_outer_index_alternatives h hTH hp m hm point mark

/-- The original right join-core order retains exactly this residual
centralizer factor and the field factor of order at most two. -/
theorem original_unitaryFour_right_core_card_alternatives :
    Nat.card ((R ⊔ sourceS L H).pCoreIn 2) =
        (2^m)^5 * Nat.card (sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) ∨
      Nat.card ((R ⊔ sourceS L H).pCoreIn 2) =
        2 * (2^m)^5 * Nat.card (sourceS L H ⊓ centralizer (L : Set G) : Subgroup G) := by
  rw [d.original_unitaryFour_join_core_card h hTH hp m hm point mark]
  rcases d.original_unitaryFour_outer_centralizer_alternatives h hTH hp m hm point mark with hc | hc
  · exact Or.inl (congrArg ((2^m)^5 * ·) hc)
  · right
    rw [hc]
    ring
/-- The remaining original centralizer acts trivially on the entire marked
native residual, with the same endpoint and full-overlap marking. -/
theorem original_unitaryFour_residual_centralizer_native_fixed
    (s : sourceS L H) (hs : s.val ∈ centralizer (L : Set G))
    (x : OriginalUnitaryFour.nativeResidual m hm point) : mark.sylowHom s x.val = x.val := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  have hLs : (L.subgroupOf P).map mark.left =
      (OriginalUnitaryFour.nativeResidual m hm point).map MulAut.conj := by
    have hr := d.original_local_eq_residual h hTH hp 0
    change L.subgroupOf P = solvableResidual P at hr
    rw [hr,mark.left_residual]
    rfl
  have hx : MulAut.conj x.val ∈ (L.subgroupOf P).map mark.left :=
    hLs.symm ▸ mem_map_of_mem MulAut.conj x.property
  obtain ⟨l,hl,hlx⟩ := hx
  let u : P := inclusion (le_sup_right.trans le_sup_left) s
  have hc : l*u=u*l := Subtype.ext (mem_centralizer_iff.mp hs l.val hl)
  have he : MulAut.conj x.val * mark.sylowHom s = mark.sylowHom s * MulAut.conj x.val := by
    rw [mark.sylowHom_left,←hlx]
    exact (map_mul mark.left l u).symm.trans ((congrArg mark.left hc).trans (map_mul mark.left u l))
  apply ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
  calc
    MulAut.conj (mark.sylowHom s x.val) =
        mark.sylowHom s * MulAut.conj x.val * (mark.sylowHom s)⁻¹ := by ext y; simp
    _ = MulAut.conj x.val := by rw [←he,mul_inv_cancel_right]
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
