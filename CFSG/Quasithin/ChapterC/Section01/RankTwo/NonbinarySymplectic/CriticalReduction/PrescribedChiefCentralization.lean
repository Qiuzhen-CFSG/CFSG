module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ChiefBudget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanNatural
public import Theory.GroupTheory.CommutatorPreimage
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanNatural

/-!
# The prescribed root pair centralizes a span modulo its original seed

A literal actor with elementary quotient image of order at least q² has
fixed index at least q² on every noncentral binary chief factor. A fixed
preimage index at most q therefore leaves no noncentral chief factor.
The residual centralizes the full normal two-group modulo the original seed.

The graph consumer uses the retained vertex projection and actual radius
span. Its SQTK hypotheses are inherited from the original input. Neither
span naturality nor a replacement of the full actor is assumed.
Source: MS93 (1.4) and (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement NoncentralChiefRefinement.SymmetricSixBudget
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

section Chief
variable {H G F : Type*} [Group H] [Finite H] [Group G] [Finite G]
  [IsSimpleGroup G] [IsQuasisimple G] [Field F] [Finite F]

private theorem prescribed_noncentralCount_eq_zero
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : Nat.card G=Nat.card (Sp F)) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (W : Subgroup H) [W.Normal] (hW : W ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizer (A : Set H)).relIndex W ≤ Nat.card F)
    (s : SeriesOn W) : s.noncentralCount=0 := by
  apply s.noncentralCount_eq_zero_iff.mpr
  intro i
  by_contra hi
  have hW2 := hp.to_le hW
  let := s.factor_elementary hW2 i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  have hl := simple_group_fixedIndex_ge_square hF hn hG hsq q hq hp A hlarge
    (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))
  change Nat.card F^2 ≤ sectionIndex A (s.lower i) (s.upper i) at hl
  have hm := sectionIndex_mul_lower_le A (s.lower i) (s.upper i) (s.series.isChief i).lt.le
  have hpos : 1 ≤ (centralizer (A : Set H)).relIndex (s.lower i).val :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu := (centralizer (A : Set H)).relIndex_le_of_le_right (s.upper_le i)
    index_ne_zero_of_finite
  have hh : Nat.card F^2 ≤ (centralizer (A : Set H)).relIndex (s.upper i).val :=
    (le_mul_of_one_le_right (by positivity) hpos).trans
      ((Nat.mul_le_mul_right _ hl).trans hm)
  have hqsize : 1<Nat.card F := Finite.one_lt_card
  have hbad : Nat.card F^2 ≤ Nat.card F := hh.trans (hu.trans hindex)
  nlinarith

private theorem prescribed_residual_commutator_eq_bot
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : Nat.card G=Nat.card (Sp F)) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (W : Subgroup H) [W.Normal] (hW : W ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizer (A : Set H)).relIndex W ≤ Nat.card F) :
    ⁅W,pResidual 2 H⁆=⊥ := by
  obtain ⟨s⟩ := SeriesOn.exists_series W
  have hs := prescribed_noncentralCount_eq_zero hF hn hG hsq q hq hp W hW A hlarge hindex s
  have hlast : IsPGroup 2 s.series.last.val := by
    rw [s.last_eq]
    exact hp.to_le hW
  have hc := s.series.residual_commutator_le_head_of_central_steps
    hlast (s.noncentralCount_eq_zero_iff.mp hs)
  rw [s.last_eq,s.head_eq] at hc
  exact le_bot_iff.mp hc

/-- A q-sized fixed-preimage budget forces residual centralization modulo
the original normal seed; only the actor's quotient image is elementary. -/
theorem prescribed_residual_commutator_le_of_fixed_index
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : Nat.card G=Nat.card (Sp F)) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (W Z : Subgroup H) [W.Normal] [Z.Normal] (hZ : Z ≤ q.ker) (hW : W ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (commutatorPreimage W A Z).relIndex W ≤ Nat.card F) :
    ⁅W,pResidual 2 H⁆ ≤ Z := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q hZ
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker=q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (W.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hWbar : W.map π ≤ qbar.ker := by rw [hker]; exact map_mono hW
  have hAbar : (A.map π).map qbar=A.map q := by rw [map_map]; rfl
  let : IsElementaryAbelian 2 ((A.map π).map qbar) := hAbar.symm ▸ inferInstance
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (W.map π) ≤ Nat.card F := by
    rw [commutatorPreimage_eq_inf_comap_centralizer,inf_relIndex_left,relIndex_comap] at hindex
    exact hindex
  have hc := prescribed_residual_commutator_eq_bot hF hn hG hsq qbar hqbar hpbar
    (W.map π) hWbar (A.map π) (hAbar.symm ▸ hlarge) hidxbar
  have hm : (⁅W,pResidual 2 H⁆).map π ≤ ⊥ := by
    rw [map_commutator,map_pResidual_quotient,hc]
  have hk := map_le_iff_le_comap.mp hm
  simpa only [MonoidHom.comap_bot,π,QuotientGroup.ker_mk'] using hk
end Chief

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction

section Graph
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- The original radius subgroup lies in the full B-preimage when its
retained elementary actor image has order at least q² but fixes index at most q. -/
theorem Input.replacement_radius_le_B_of_prescribed_fixed_index
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {v : Vertex d.radical} (hv : color d.radical v=false)
    (W A : Subgroup (FreeAmalgam d.radical))
    (hWV : W ≤ V d.radical v)
    (hSW : stabilizer d.radical v ≤ normalizer (W : Set (FreeAmalgam d.radical)))
    (hAS : A ≤ stabilizer d.radical v)
    (E : BinaryField) (hE : E.degree=n)
    (f : stabilizer d.radical v →* Sp E.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical v).subtype=Q d.radical v)
    (hEA : IsElementaryAbelian 2 ((A.subgroupOf (stabilizer d.radical v)).map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical v).relIndex A)
    (hindex : (commutatorPreimage W A (Z d.radical v)).relIndex W ≤ Nat.card F) :
    W ≤ B d.radical v (geometry.Z_normal v) := by
  let S := stabilizer d.radical v
  let W₀ := W.subgroupOf S
  let Z₀ := (Z d.radical v).subgroupOf S
  let A₀ := A.subgroupOf S
  let C := commutatorPreimage W A (Z d.radical v)
  let C₀ := C.subgroupOf S
  let := finite_stabilizer d.radical v
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hSW
  let : Z₀.Normal := normal_subgroupOf_of_le_normalizer (Z_normalized d.radical v)
  have hWQ : W ≤ Q d.radical v := hWV.trans (geometry.V_le_Q (by omega) v hv)
  have hWS : W ≤ S := hWQ.trans (fun _ hx => hx.1)
  have hZS : Z d.radical v ≤ S := Z_le_stabilizer d.radical v
  have hCS : C ≤ S := (commutatorPreimage_le _ _ _).trans hWS
  have hker : f.ker=(Q d.radical v).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) v hv).comap_subtype
  have hqsize : 3<Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3<2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := SimpleQuotients.isSimpleGroup hqsize
  let : IsSimpleGroup (Sp E.Carrier) := EvenProjective.equiv.isSimpleGroup
  let : IsQuasisimple (Sp E.Carrier) := CentralCovers.Even.isQuasisimple hqsize
  let : IsElementaryAbelian 2 (A₀.map f) := hEA
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hAcard : Nat.card E.Carrier^2 ≤ Nat.card (A₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hAS] at hh
    rw [←hh,hcard]
    exact hlarge
  have hCcomm : ⁅C,A⁆ ≤ Z d.radical v :=
    commutator_commutatorPreimage_le W A (Z d.radical v) (hWS.trans (Z_normalized d.radical v))
  have hC₀comm : ⁅C₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hCS,map_subgroupOf_eq_of_le hAS,
      map_subgroupOf_eq_of_le hZS]
    exact hCcomm
  have hpre : C₀ ≤ commutatorPreimage W₀ A₀ Z₀ :=
    le_commutatorPreimage (comap_mono (commutatorPreimage_le _ _ _)) hC₀comm
  have hidx₀ : (commutatorPreimage W₀ A₀ Z₀).relIndex W₀ ≤ Nat.card E.Carrier := by
    have hh : C₀.relIndex W₀ ≤ Nat.card F := by
      have he := relIndex_map_map_of_injective C₀ W₀ S.subtype_injective
      rw [map_subgroupOf_eq_of_le hCS,map_subgroupOf_eq_of_le hWS] at he
      rw [←he]
      exact hindex
    rw [hcard]
    exact (relIndex_le_of_le_left hpre (L := W₀) index_ne_zero_of_finite).trans hh
  have hcomm := prescribed_residual_commutator_le_of_fixed_index
    (show Nat.card E.Carrier=2^n by rw [E.card_eq,hE]) h.nonbinary rfl
    (actual_vertex_projection_sqtk h d hv E f hf hfQ) f hf hp W₀ Z₀
    (by rw [hker]; exact comap_mono ((Z_le_VBall d.radical v 2).trans
      (geometry.V_le_Q (by omega) v hv)))
    (by rw [hker]; exact comap_mono hWQ) A₀ hAcard hidx₀
  have hamb := map_mono (f := S.subtype) hcomm
  rw [map_commutator,map_subgroupOf_eq_of_le hWS,map_subgroupOf_eq_of_le hZS] at hamb
  exact radius_le_B_of_commutator geometry (by omega) hv W hWV hamb

/-- The actual critical span cannot have the prescribed q budget under
an elementary root-pair image of order at least q². -/
theorem Input.replacement_critical_span_prescribed_fixed_index_false
    {geometry : Geometry d.radical} {v e : Vertex d.radical}
    (back : CriticalPath d.radical geometry v e) (hb : geometry.b d.radical=4)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical v)
    (E : BinaryField) (hE : E.degree=n)
    (f : stabilizer d.radical v →* Sp E.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical v).subtype=Q d.radical v)
    (hEA : IsElementaryAbelian 2 ((A.subgroupOf (stabilizer d.radical v)).map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical v).relIndex A)
    (hindex : (commutatorPreimage (localZSpan d.radical (back.walk.getVert 2) v) A
      (Z d.radical v)).relIndex (localZSpan d.radical (back.walk.getVert 2) v) ≤ Nat.card F) : False := by
  let a := back.walk.getVert 2
  let W := localZSpan d.radical a v
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl := back.length_eq_b
  have hva : (cosetGraph d.radical).dist v a=2 := back.dist_start (by omega)
  have hWB := h.replacement_radius_le_B_of_prescribed_fixed_index d geometry hb4 back.start_color
    W A (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hva]))
    (localZSpan_normalized d.radical a v) hAS E hE f hf hfQ hEA hlarge hindex
  have hU : U d.radical a ≤ B d.radical v (geometry.Z_normal v) :=
    (U_le_Z a).trans ((Z_le_localZSpan d.radical a v).trans hWB)
  have hi := h.replacement_path_moving_index_ge_field d back hb4
  rw [relIndex_eq_one.mpr hU] at hi
  exact (not_le_of_gt (Finite.one_lt_card (α := F))) hi
end Graph

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
