module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoPlacements
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.NormalizerInnerAutomorphisms

/-!
# Full radical-normalizer control in the ordinary J4 component

Every automorphism of the actual J4 model is inner. Perfect central-cover
rigidity lifts innerness to the original component K. For the original radical
R, its projection to K along the centralizer is a two-group: the kernel is
Z(K), which is a two-group. This projection is normalized by N_H(R), so
radicality puts it inside R. Hence R splits across K and C_H(K), and
N_K(R intersect K) normalizes R and lies in the original M.

Since Z(K) lies in R intersect K, the full normalizer passes through the
literal central quotient. It therefore normalizes the same covering residual.
The first involution-centralizer type is excluded by its normal-perfect
subgroup eleven divisor. Both the B=L and odd-normalizer consumers retain
full W; no shortness, W=V, order-64 or full-Sylow premise is used.

Exhaustive placement of this normalizer remains with
qt-d-1222-natural-point-fixed-summand, together with degree-two centralizer
control and 11.1.5. The odd-normalizer owner independently handles its outer
and moved cases. Earlier-source discharge remains with
qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith C.2.1--2 and C.3.1--5, pp.144--151;
the ordinary local inspections on pp.611--612 and622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem radical_component_factor
    {A : Type*} [Group A] [Finite A] (K R : Subgroup A) [K.Normal]
    (hR : IsPRadical 2 R) (hz : IsPGroup 2 (center K))
    (hinner : R ≤ K ⊔ centralizer (K : Set A)) :
    R = (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set A)) := by
  let C := centralizer (K : Set A)
  let q := QuotientGroup.mk' C
  let f := q.comp K.subtype
  have hk : f.ker = center K := by
    ext k
    change (QuotientGroup.mk (k : A) : A ⧸ C) = 1 ↔ k ∈ center K
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact mem_center_iff.mpr fun x => Subtype.ext (h x x.property)
    · intro h x hx
      exact congrArg K.subtype (mem_center_iff.mp h ⟨x,hx⟩)
  have hp : IsPGroup 2 ((R.map q).comap f) :=
    (hR.isPGroup.map q).comap_of_ker_isPGroup f (hk ▸ hz)
  have he : ((R.map q).comap f).map K.subtype = K ⊓ (R ⊔ C) := by
    change (((R.map q).comap q).subgroupOf K).map K.subtype = _
    rw [subgroupOf_map_subtype,comap_map_eq,QuotientGroup.ker_mk',inf_comm]
  have hQ : IsPGroup 2 ↥(K ⊓ (R ⊔ C) : Subgroup A) := he ▸ hp.map K.subtype
  have hn : normalizer (R : Set A) ≤ normalizer ((K ⊓ (R ⊔ C) : Subgroup A) : Set A) :=
    (le_inf le_normalizer_of_normal normalizer_le_normalizer_sup_normal).trans
      inf_normalizer_le_normalizer_inf
  have hQR := le_of_normalizer_le_normalizer_of_pCore_normalizer_le R _
    hR.isPGroup hQ hR.2.le hn
  apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro r hr
  obtain ⟨k,hk,c,hc,hkc⟩ := mem_sup_of_normal_right.mp (hinner hr)
  have hkR : k ∈ R := by
    apply hQR
    refine ⟨hk,?_⟩
    have heq : k = r * c⁻¹ := by rw [←hkc]; group
    rw [heq]
    exact mul_mem (mem_sup_left hr) (mem_sup_right (C.inv_mem hc))
  have hcR : c ∈ R := by
    have heq : c = k⁻¹ * r := by rw [←hkc]; group
    rw [heq]
    exact R.mul_mem (R.inv_mem hkR) hr
  rw [←hkc]
  exact mul_mem (mem_sup_left ⟨hkR,hk⟩) (mem_sup_right ⟨hcR,hc⟩)

private theorem janko_cover_all_inner
    {A : Type*} [Group A] [Group.IsPerfect A]
    (e : A ⧸ center A ≃* Janko4.Model) (a : MulAut A) :
    ∃ k : A, a = MulAut.conj k := by
  apply (MulAut.centralQuotientAction_inner_iff e a).mp
  exact Janko4.AdequateLocal.exists_eq_conj _

variable {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}

/-- Innerness in the actual J4 central quotient lifts to the original component,
so the actual radical splits across that component and its centralizer. -/
theorem ordinary_jankoFour_radical_factor
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    R.subgroupOf H = (R.subgroupOf H ⊓ K) ⊔
      (R.subgroupOf H ⊓ centralizer (K : Set H)) := by
  let := h.ordinary_component_normal K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  apply radical_component_factor K (R.subgroupOf H) h.isRadical
    (hz ▸ pCore_isPGroup)
  intro r _
  let n : normalizer (K : Set H) := ⟨r,by rw [normalizer_eq_top]; trivial⟩
  obtain ⟨k,hk⟩ := janko_cover_all_inner e (K.normalizerMonoidHom n)
  have hi : n ∈ (MulAut.conj : K →* MulAut K).range.comap K.normalizerMonoidHom :=
    ⟨k,hk.symm⟩
  rw [normalizerMonoidHom_comap_conj_range] at hi
  exact hi

/-- The full normalizer inside the component of the original radical intersection
lies in M. This uses innerness and radicality, not full Sylow containment. -/
theorem ordinary_jankoFour_component_radical_normalizer_control
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    normalizer (ordinaryComponentSubgroup R K : Set K) ≤ ordinaryComponentSubgroup M K := by
  have he := ordinary_jankoFour_radical_factor h K hK e
  have hc : K ≤ normalizer
      ((R.subgroupOf H ⊓ centralizer (K : Set H) : Subgroup H) : Set H) :=
    (le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hn : K ⊓ normalizer ((R.subgroupOf H ⊓ K : Subgroup H) : Set H) ≤
      normalizer (R.subgroupOf H : Set H) := by
    have hsup := (le_inf (show K ⊓ normalizer ((R.subgroupOf H ⊓ K : Subgroup H) : Set H) ≤
        normalizer ((R.subgroupOf H ⊓ K : Subgroup H) : Set H) from inf_le_right)
      (inf_le_left.trans hc)).trans
      (normalizer_inf_normalizer_le_normalizer_sup (R.subgroupOf H ⊓ K)
        (R.subgroupOf H ⊓ centralizer (K : Set H)))
    rwa [←he] at hsup
  intro k hk
  change k ∈ normalizer ((R.subgroupOf H).subgroupOf K : Set K) at hk
  rw [←inf_subgroupOf_right (R.subgroupOf H) K,
    ←subgroupOf_normalizer_eq inf_le_right] at hk
  have hr := hn ⟨k.property,hk⟩
  rw [←subgroupOf_normalizer_eq (h.radical_le.trans h.local_le)] at hr
  exact h.normalizer_le ⟨k.val.property,hr⟩

/-- The full radical normalizer after central projection is controlled by the
literal projected M. The central kernel lies in the radical by radicality. -/
theorem ordinary_jankoFour_projected_radical_normalizer_control
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    normalizer (((ordinaryComponentSubgroup R K).map
      (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) ≤
      (ordinaryComponentSubgroup M K).map (QuotientGroup.mk' (center K)) := by
  let q := QuotientGroup.mk' (center K)
  let P := ordinaryComponentSubgroup R K
  have hr := h.ordinary_radical_intersection_isRadical K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hc : q.ker ≤ P := by
    rw [QuotientGroup.ker_mk',hz]
    exact pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hn : (normalizer (P.map q : Set (K ⧸ center K))).comap q =
      normalizer (P : Set K) := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq_self hc]
  have hm := congrArg (map q) hn
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  rw [hm]
  exact map_mono (ordinary_jankoFour_component_radical_normalizer_control h K hK e)

/-- The actual projected radical normalizer preserves the original covering residual. -/
theorem ordinary_jankoFour_radical_normalizer_le_residual_normalizer
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    normalizer (((ordinaryComponentSubgroup R K).map
      (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) ≤
      normalizer ((ordinaryCoverProjection h K hK).range : Set (K ⧸ center K)) := by
  rw [ordinary_projected_normalizer h hn K hK]
  exact ordinary_jankoFour_projected_radical_normalizer_control h K hK e


/-- The first centralizer cannot be the abstract type of the full radical
normalizer: its normal perfect subgroups have an eleven divisor. -/
theorem janko_radical_normalizer_not_equiv_first
    (F : CFSG.Quasithin.ChapterB.QuasisimpleSource.BinaryField) (hF : F.degree = 2)
    (P X : Subgroup Janko4.Model) [Group.IsPerfect X]
    (hXN : X ≤ normalizer (P : Set Janko4.Model))
    (hNX : normalizer (P : Set Janko4.Model) ≤ normalizer (X : Set Janko4.Model))
    (a : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (e : normalizer (P : Set Janko4.Model) ≃* Janko4.InvolutionCentralizers.First.centralizer) :
    False := by
  let Y := X.subgroupOf (normalizer (P : Set Janko4.Model))
  let : Y.Normal := normal_subgroupOf_of_le_normalizer hNX
  let b := subgroupOfEquivOfLe hXN
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  let Z := Y.map e.toMonoidHom
  let : Z.Normal := (inferInstance : Y.Normal).map e.toMonoidHom e.surjective
  let : Group.IsPerfect Z := Group.IsPerfect.map e.toMonoidHom
  let c : Z ≃* X := (e.subgroupMap Y).symm.trans b
  let q := c.toMonoidHom.quotientPCoreEquivOfSurjective c.surjective
    (by rw [c.toMonoidHom.ker_eq_bot c.injective]; exact IsPGroup.of_subsingleton 2 _)
  exact janko_first_centralizer_no_normal_full_linear_three F hF Z (q.trans a)

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation

/-- The actual C.2.8 covering residual excludes the first-centralizer type
for its full projected radical normalizer, with no assumed local placement. -/
theorem c28_covering_jankoFour_radical_normalizer_not_equiv_first
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    ¬ Nonempty (normalizer (((ordinaryComponentSubgroup R K).map
        (QuotientGroup.mk' (center K))).map ek.toMonoidHom : Set Janko4.Model) ≃*
      Janko4.InvolutionCentralizers.First.centralizer) := by
  rintro ⟨b⟩
  obtain ⟨_,hf,_,_,a,_,_⟩ := c28_covering_jankoFour_local D S h hstrict hn hBL hc hVB e he K hK
  let P₀ := (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))
  let X₀ := (ordinaryCoverProjection h K hK).range
  let X := X₀.map ek.toMonoidHom
  let P := P₀.map ek.toMonoidHom
  let t := ek.subgroupMap X₀
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  let : Group.IsPerfect X₀ := (ordinary_projected_geometry h hn K hK).1
  let : Group.IsPerfect X := Group.IsPerfect.map ek.toMonoidHom
  have hXN : X ≤ normalizer (P : Set Janko4.Model) := by
    rw [←map_equiv_normalizer_eq P₀ ek]
    exact map_mono (ordinary_projected_cover_normalizes_radical h hn K hK)
  have hNX : normalizer (P : Set Janko4.Model) ≤ normalizer (X : Set Janko4.Model) := by
    rw [←map_equiv_normalizer_eq P₀ ek,←map_equiv_normalizer_eq X₀ ek]
    exact map_mono (ordinary_jankoFour_radical_normalizer_le_residual_normalizer h hn K hK ek)
  exact janko_radical_normalizer_not_equiv_first S.field hf P X hXN hNX (q.symm.trans a) b


/-- The odd-normalizer consumer uses its actual covering residual and full W.
The outer and moved-component cases are outside this C.2.8 application. -/
theorem pushingUp_jankoFour_radical_normalizer_control
    {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : OddNormalizer.PushingUpFieldFourCase D S A) :
    ∃ J H W : Subgroup G,
      Chapter4.PushLE L (Chapter4.Section04.oddActorResidual L A) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧
      let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let M := H ⊓ normalizer (L : Set G)
      let R := J.pCoreIn 2
      ∃ (hC : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
        (K : Subgroup H) (hK : IsComponent H K) (ek : K ⧸ center K ≃* Janko4.Model),
        normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) ≤
          normalizer ((ordinaryCoverProjection hC K hK).range : Set (K ⧸ center K)) ∧
        ¬ Nonempty (normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))).map ek.toMonoidHom : Set Janko4.Model) ≃*
          Janko4.InvolutionCentralizers.First.centralizer) := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,_,hC,hcover,hN,hVB,⟨e,he⟩,_,_,_,
    _,_,_,K,hK,_,_,_,_,_⟩ := h
  have hBL := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_left
  obtain ⟨⟨ek⟩,_,_,_⟩ := c28_covering_ordinary_jankoFour D S hC hBL hcover hVB e K hK
  exact ⟨J,H,W,hpush,hH,hJH,hC,K,hK,ek,
    ordinary_jankoFour_radical_normalizer_le_residual_normalizer hC hN K hK ek,
    c28_covering_jankoFour_radical_normalizer_not_equiv_first D S hC hstrict hN
      hBL hcover hVB e he K hK ek⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
