module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFirstCore
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupAction.Order512FiveStructure

/-!
# Class three of the actual Ru five-residual

For the original Q₅=[Q,B₅], the derived subgroup is U, the Frattini
subgroup is U, the center is Z, and the nilpotency class is three.
All subgroup images and the five-action retain their original markings.

The crucial exclusion of class two uses the original indecomposable
six-dimensional action, rather than the class of the larger first core.
J.2.4 identifies the kernel of each nonzero HC/U commutator row modulo Z
with HC. If Q₅ were class two, a second subgroup of order512 with derived
group in Z could intersect it only in U. Their orders force an intersection
of at least128, whereas |U|=32. Consequently Q₅ would be H-invariant;
its image and HC/U would then split the indecomposable six-space.

The literal B₅ conjugation action now satisfies Parrott's order512 theorem:
its fixed subgroup lies in Q₅∩C_Q(B₅)=Z. This gives class three and derived
order32. The existing elementary Q/U identifies that derived subgroup
with the original U. `Q₅_source_structure` supplies the residual layers
required by the first Ree endpoint and its semilinear frame construction.

Source: Aschbacher–Smith Ru2, J.2.4, J.4.1(3), and J.4.4–5,
printed pp.431,434,440–442; Parrott (1972), Lemma1, p.672.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices Fusion
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

private theorem HC_derived_le_Z :
    ⁅d.toTypeRuSetup.HC,d.toTypeRuSetup.HC⁆≤d.toTypeRuSetup.Z := by
  obtain ⟨c⟩ := SourceCompletion.exists_choices d
  have hPhi := (SourceCompletion.fusion c).2.2.1.2.2.2.2.1
  exact derived_le_of_frattini_image_le
    ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
      (inclusion d.toTypeRuSetup.HC_le_Q) (inclusion_injective _)) hPhi.le

theorem HC_commutator_mem_Z_iff (c : G) (hc : c∈d.toTypeRuSetup.HC)
    (hcu : c∉d.toTypeRuSetup.U) (q : d.toTypeRuSetup.Q) :
    ⁅c,(q:G)⁆∈d.toTypeRuSetup.Z ↔ (q:G)∈d.toTypeRuSetup.HC := by
  let D := d.toTypeRuSetup
  let : IsElementaryAbelian 2 D.U := d.elementary_U
  have hCQ : ⁅D.HC,D.Q⁆≤D.U := by
    rw [commutator_comm]
    exact commutator_le.mpr fun q hq c hc => d.HC_commutator_K_mem_U ⟨c,hc⟩ ⟨q,d.Q_le_K hq⟩
  have hUQ : ⁅D.U,D.Q⁆≤D.Z := by
    rw [commutator_comm]
    exact D.commutator_Q_U_le_Z
  let f := commutatorRow D d.U_le_HC hCQ hUQ ⟨c,hc⟩
  have hmem (q:D.Q) : q∈f.ker ↔ ⁅c,(q:G)⁆∈D.Z := by
    change f q=1 ↔ _
    rw [commutatorRow_apply]
    exact QuotientGroup.eq_one_iff _
  obtain ⟨a⟩ := SourceCompletion.exists_choices d
  have hfr : f.range=modZ D D.U :=
    (commutatorRow_range D d.U_le_HC hCQ hUQ ⟨c,hc⟩).trans
      ((SourceCompletion.fusion a).1 c hc hcu).1
  have hkcard : Nat.card f.ker=128 := by
    have h := f.ker.index_mul_card
    rw [index_ker,hfr,card_modZ_U D d.card_Z,d.ru2.card_Q d.card_Z] at h
    omega
  have hk : D.HC.subgroupOf D.Q=f.ker := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact (hmem x).mpr (HC_derived_le_Z d (commutator_mem_commutator hc hx))
    · rw [hkcard,Nat.card_congr (subgroupOfEquivOfLe d.toTypeRuSetup.HC_le_Q).toEquiv,
        d.card_HC]
  exact (hmem q).symm.trans (by rw [←hk]; rfl)

theorem Q₅_inf_HC : Q₅ d B5⊓d.toTypeRuSetup.HC=d.toTypeRuSetup.U := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q₅ d B5)
    d.toTypeRuSetup.HC (d.toTypeRuSetup.HC_le_Q.trans (Q₅_normalized d B5))
  rw [Q₅_sup_HC,card_Q₅,d.card_HC,d.ru2.card_Q d.card_Z] at h
  apply (eq_of_le_of_card_ge (le_inf (U_le_Q₅ d B5) d.U_le_HC) ?_).symm
  change Nat.card (Q₅ d B5⊓d.toTypeRuSetup.HC:Subgroup G)≤Nat.card d.toTypeRuSetup.U
  rw [d.ru2.card_U d.card_Z]
  omega

private theorem quotient_commute_of_commutator (x y : d.toTypeRuSetup.H)
    (h : ⁅(x:G),(y:G)⁆∈d.toTypeRuSetup.Z) :
    Commute (centerQuotientMap d.toTypeRuSetup x) (centerQuotientMap d.toTypeRuSetup y) := by
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr h

/-- Under the class-two alternative, Q₅ is the unique subgroup of its order
whose commutators lie in Z. J.2.4 excludes distinct such subgroups. -/
theorem Q₅_unique_of_derived_le_Z
    (hP : ⁅Q₅ d B5,Q₅ d B5⁆≤d.toTypeRuSetup.Z)
    (N : Subgroup G) (hNQ : N≤d.toTypeRuSetup.Q) (hNcard : Nat.card N=512)
    (hN : ⁅N,N⁆≤d.toTypeRuSetup.Z) : N=Q₅ d B5 := by
  have hle : N≤Q₅ d B5 := by
    by_contra hn
    obtain ⟨a,ha,haP⟩ := Set.not_subset.mp hn
    have hap : a∈(↑(Q₅ d B5):Set G)*(↑(CQ B5):Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (Q₅ d B5) (CQ B5)
        ((show CQ B5≤d.toTypeRuSetup.Q from inf_le_left).trans (Q₅_normalized d B5)),
        ←Q_eq_Q₅_sup_CQ]
      exact hNQ ha
    obtain ⟨p,hp,c,hc,hpc⟩ := hap
    have hcHC := five_centralizer_le_HC B5 hc
    have hcU : c∉d.toTypeRuSetup.U := by
      intro hu
      exact haP (hpc ▸ (Q₅ d B5).mul_mem hp (U_le_Q₅ d B5 hu))
    have hInf : Q₅ d B5⊓N≤d.toTypeRuSetup.U := by
      intro x hx
      have hxQ := Q₅_le_Q d B5 hx.1
      have hxHC : x∈d.toTypeRuSetup.HC := by
        apply (HC_commutator_mem_Z_iff d c hcHC hcU ⟨x,hxQ⟩).mp
        let xH : d.toTypeRuSetup.H := ⟨x,pCoreIn_le 2 _ hxQ⟩
        let pH : d.toTypeRuSetup.H := ⟨p,pCoreIn_le 2 _ (Q₅_le_Q d B5 hp)⟩
        let aH : d.toTypeRuSetup.H := ⟨a,pCoreIn_le 2 _ (hNQ ha)⟩
        have hpx := quotient_commute_of_commutator d pH xH
          (hP (commutator_mem_commutator hp hx.1))
        have hax := quotient_commute_of_commutator d aH xH
          (hN (commutator_mem_commutator ha hx.2))
        have hcx := hpx.inv_left.mul_left hax
        have hce : pH⁻¹*aH=(⟨c,hcHC.1⟩:d.toTypeRuSetup.H) := by
          apply Subtype.ext
          change p⁻¹*a=c
          rw [←hpc,inv_mul_cancel_left]
        rw [←map_inv,←map_mul,hce] at hcx
        change (⁅(⟨c,hcHC.1⟩:d.toTypeRuSetup.H),xH⁆)∈d.toTypeRuSetup.Z.subgroupOf d.toTypeRuSetup.H
        apply (QuotientGroup.eq_one_iff _).mp
        change centerQuotientMap d.toTypeRuSetup ⁅(⟨c,hcHC.1⟩:d.toTypeRuSetup.H),xH⁆=1
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcx.eq
      exact (Q₅_inf_HC d B5).le ⟨hx.1,hxHC⟩
    have hi := card_le_of_le hInf
    have hs := card_le_of_le (sup_le (Q₅_le_Q d B5) hNQ)
    have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q₅ d B5) N
      (hNQ.trans (Q₅_normalized d B5))
    rw [card_Q₅,hNcard] at hm
    rw [d.ru2.card_U d.card_Z] at hi
    rw [d.ru2.card_Q d.card_Z] at hs
    nlinarith [Nat.mul_le_mul hi hs]
  exact eq_of_le_of_card_ge hle (by rw [card_Q₅,hNcard])

theorem Q₅_normalized_by_H_of_derived_le_Z
    (hP : ⁅Q₅ d B5,Q₅ d B5⁆≤d.toTypeRuSetup.Z) :
    d.toTypeRuSetup.H≤normalizer (Q₅ d B5) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  apply Q₅_unique_of_derived_le_Z d B5 hP
  · rintro _ ⟨x,hx,rfl⟩
    exact (mem_normalizer_iff.mp (d.ru2.six.normalized hg) x).mp (Q₅_le_Q d B5 hx)
  · rw [card_map_of_injective (MulAut.conj g).injective,card_Q₅]
  · rw [←map_commutator]
    rintro _ ⟨x,hx,rfl⟩
    change g*x*g⁻¹∈d.toTypeRuSetup.Z
    have he : x*g=g*x := hg x (hP hx)
    simpa only [←he,mul_assoc,mul_inv_cancel,mul_one] using hP hx

/-- A normal Q₅ would split the original indecomposable six-space. -/
theorem Q₅_not_normalized_by_H :
    ¬d.toTypeRuSetup.H≤normalizer (Q₅ d B5) := by
  intro hP
  have hC : d.toTypeRuSetup.H≤normalizer d.toTypeRuSetup.HC :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.toTypeRuSetup.HC_normal
  have hinv (N:Subgroup G) (hN:d.toTypeRuSetup.H≤normalizer N) :
      ∀g v,v∈d.ru2.six.imageSpace N → d.ru2.sixAction g v∈d.ru2.six.imageSpace N := by
    intro g v hv
    obtain ⟨h,rfl⟩ := d.ru2.quotient_surjective g
    obtain ⟨q,hq,rfl⟩ := (d.ru2.six.mem_imageSpace_iff N v).mp hv
    exact (d.ru2.six.mem_imageSpace_iff N _).mpr
      ⟨⟨h*q*(h:G)⁻¹,(mem_normalizer_iff.mp (d.ru2.six.normalized h.property) q).mp q.property⟩,
        (mem_normalizer_iff.mp (hN h.property) q).mp hq,d.ru2.six.equivariant h q⟩
  have hbot (N:Subgroup G) (hN:N≤d.toTypeRuSetup.Q)
      (h:d.ru2.six.imageSpace N=⊥) : N≤d.toTypeRuSetup.U := by
    intro x hx
    have hm := (d.ru2.six.mem_imageSpace_iff N _).mpr
      ⟨⟨x,hN hx⟩,hx,rfl⟩
    rw [h,Submodule.mem_bot] at hm
    exact (d.ru2.six.coordinates_eq_one_iff ⟨x,hN hx⟩).mp hm
  have hc := d.ru2.six.isCompl_imageSpace (Q₅ d B5) d.toTypeRuSetup.HC
    (Q₅_sup_HC d B5).symm (Q₅_inf_HC d B5).symm
  rcases d.ru2.indecomposable _ _ (hinv _ hP) (hinv _ hC) hc with hp | hc
  · have hh := card_le_of_le (hbot _ (Q₅_le_Q d B5) hp)
    rw [card_Q₅,d.ru2.card_U d.card_Z] at hh
    omega
  · have hh := card_le_of_le (hbot _ d.toTypeRuSetup.HC_le_Q hc)
    rw [d.card_HC,d.ru2.card_U d.card_Z] at hh
    omega

/-- The actual residual derived group is not central. -/
theorem Q₅_derived_not_le_Z :
    ¬⁅Q₅ d B5,Q₅ d B5⁆≤d.toTypeRuSetup.Z :=
  fun h => Q₅_not_normalized_by_H d B5 (Q₅_normalized_by_H_of_derived_le_Z d B5 h)

theorem Q₅_class_at_least_three : 3≤Group.nilpotencyClass (Q₅ d B5) := by
  let P:=Q₅ d B5
  let : Group.IsNilpotent P := ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
    (inclusion (Q₅_le_Q d B5)) (inclusion_injective _)).isNilpotent
  by_contra hn
  have hle : Group.nilpotencyClass P≤2 := by change Group.nilpotencyClass (Q₅ d B5)≤2; omega
  have hbot := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hle
  have hc : _root_.commutator P≤center P :=
    commutator_top_right_eq_bot_iff_le_center.mp hbot
  apply Q₅_derived_not_le_Z d B5
  rw [←map_subtype_commutator]
  rintro _ ⟨x,hx,rfl⟩
  apply (centralizer_Q₅ d B5).le
  intro y hy
  exact congrArg (fun a:P=>(a:G)) (mem_center_iff.mp (hc hx) ⟨y,hy⟩)

theorem Q₅_inf_CQ : Q₅ d B5⊓CQ B5=d.toTypeRuSetup.Z := by
  have h : Q₅ d B5⊓CQ B5=(Q₅ d B5⊓d.toTypeRuSetup.HC)⊓CQ B5 := by
    rw [inf_assoc,inf_eq_right.mpr (five_centralizer_le_HC B5)]
  rw [h,Q₅_inf_HC,inf_comm,five_centralizer_inf_U]

theorem Q₅_parrott_structure :
    Group.nilpotencyClass (Q₅ d B5)=3 ∧ Nat.card (center (Q₅ d B5))=2 ∧
    _root_.commutator (Q₅ d B5)=frattini (Q₅ d B5) ∧
    _root_.commutator (Q₅ d B5)=Subgroup.upperCentralSeries (Q₅ d B5) 2 ∧
    IsElementaryAbelian 2 (_root_.commutator (Q₅ d B5)) ∧
    Nat.card (_root_.commutator (Q₅ d B5))=32 := by
  let P:=Q₅ d B5
  let A:=B5Image B5
  let : MulDistribMulAction A P := conjMulDistribMulActionOfLeNormalizer A P
    (normalizer_commutator_ge_right _ _)
  apply Theory.GroupAction.parrott_twoGroup_structure
    ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
      (inclusion (Q₅_le_Q d B5)) (inclusion_injective _))
    (card_Q₅ d B5) (Q₅_class_at_least_three d B5) (B5Image_card d.card_Z B5)
  intro x hx
  have hxc : (x:G)∈CQ B5 := by
    refine ⟨Q₅_le_Q d B5 x.property,?_⟩
    intro a ha
    have he := congrArg (fun y:P=>(y:G)) (hx ⟨a,ha⟩)
    change a*(x:G)*a⁻¹=(x:G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hxZ : (x:G)∈d.toTypeRuSetup.Z := (Q₅_inf_CQ d B5).le ⟨x.property,hxc⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact ((pCoreIn_le 2 _ (Q₅_le_Q d B5 y.property)) (x:G) hxZ).symm

theorem Q₅_derived_eq_U : ⁅Q₅ d B5,Q₅ d B5⁆=d.toTypeRuSetup.U := by
  apply eq_of_le_of_card_ge
  · rw [←firstCore_derived d B5]
    exact commutator_mono le_sup_right le_sup_right
  · rw [←map_subtype_commutator,card_map_of_injective (Q₅ d B5).subtype_injective,
      (Q₅_parrott_structure d B5).2.2.2.2.2,d.ru2.card_U d.card_Z]

theorem Q₅_frattini_eq_U :
    (frattini (Q₅ d B5)).map (Q₅ d B5).subtype=d.toTypeRuSetup.U := by
  rw [←(Q₅_parrott_structure d B5).2.2.1,map_subtype_commutator,Q₅_derived_eq_U]

theorem Q₅_center_eq_Z :
    (center (Q₅ d B5)).map (Q₅ d B5).subtype=d.toTypeRuSetup.Z := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply (centralizer_Q₅ d B5).le
    intro y hy
    exact congrArg (fun a:Q₅ d B5=>(a:G)) (mem_center_iff.mp hx ⟨y,hy⟩)
  · intro z hz
    refine ⟨⟨z,U_le_Q₅ d B5 (d.ru2.natural.kernel_le hz)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((pCoreIn_le 2 _ (Q₅_le_Q d B5 y.property)) z hz).symm

/-- The actual residual and actual first core have the same derived subgroup,
with elementary derived layer U and the original central line Z. -/
theorem Q₅_source_structure :
    Nat.card (Q₅ d B5)=512 ∧ Group.nilpotencyClass (Q₅ d B5)=3 ∧
    ⁅Q₅ d B5,Q₅ d B5⁆=d.toTypeRuSetup.U ∧
    (frattini (Q₅ d B5)).map (Q₅ d B5).subtype=d.toTypeRuSetup.U ∧
    (center (Q₅ d B5)).map (Q₅ d B5).subtype=d.toTypeRuSetup.Z ∧
    ⁅Q₅ d B5,Q₅ d B5⁆=⁅fiveHyperplane d B5,fiveHyperplane d B5⁆ ∧
    Q₅ d B5⊓centralizer (d.toTypeRuSetup.U:Set G)=d.toTypeRuSetup.U := by
  refine ⟨card_Q₅ d B5,(Q₅_parrott_structure d B5).1,Q₅_derived_eq_U d B5,
    Q₅_frattini_eq_U d B5,Q₅_center_eq_Z d B5,?_,?_⟩
  · rw [Q₅_derived_eq_U,firstCore_derived]
  · rw [centralizer_U,Q₅_inf_HC]

end CFSG.Quasithin.ChapterJ.RuSubgroup
