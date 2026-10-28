module
public import Theory.GroupTheory.ElementaryEightCentralizerOrder
public import Theory.GroupTheory.CentralCommutatorEightCenter
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.Group

/-!
# A point centralizer in an extension of a central elementary eight

Let R of order thirty-two be normal in Q of order at most sixty-four.
An elementary V of order eight is self-centralizing in R; the center Z
of R has order two and contains its derived subgroup. Suppose Q fixes Z
and acts trivially on V/Z. For an involution a in Q, put C=C_Q(V).
If C_C(a) is an order-four subgroup L of V and every [a,c] lies in L,
then C_Q(a) is contained in R. All subgroups and commutators are literal
ambient ones, and no extraspecial classification or complement is assumed.

Unless Q=R, the central-line action count gives |C|=16 and the normalized
product formula gives Q=RC. The central elementary subgroup V has index
two in C. Normalization puts [C,R] in V, so its exponent two makes C²
centralize R; hence C² lies in Z. The same argument gives R²≤Z.
The commutator homomorphism C→L has kernel L, so it is surjective and
its inverse image of Z is precisely V. A square-product identity first
puts a in R. Factoring an arbitrary element of C_Q(a) through RC and
using [R,R]≤Z then puts its C component in V, giving the conclusion.

This source-neutral calculation supplies the omitted terminal-core
centralizer step in Stellmacher (10.1)(a3)(11), Journal of Algebra190
(1997), printed p.62. Its application separately proves the actual graph
subgroup hypotheses, including the fixed subgroup L.
-/

open scoped commutatorElement Pointwise
set_option maxHeartbeats 800000
namespace Subgroup

private theorem square_product_commutator_mem
    {G : Type*} [Group G] (Z : Subgroup G) (r c : G)
    (hr : r^2∈Z) (hc : c^2∈Z)
    (hcentral : ∀z∈Z,Commute z c) (hprod : (r*c)^2=1) : ⁅r*c,c⁆∈Z := by
  have hs : r*c*r=c⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa only [pow_two,mul_assoc] using hprod
  have hrinv : r⁻¹=r*(r^2)⁻¹ := by group
  have hmove : (r^2)⁻¹*c⁻¹=c⁻¹*(r^2)⁻¹ := (hcentral _ hr).inv_inv.eq
  have he : ⁅r*c,c⁆=(c^2)⁻¹*(r^2)⁻¹ := by
    calc
      ⁅r*c,c⁆ = r*c*r⁻¹*c⁻¹ := by simp only [commutatorElement_def]; group
      _ = (r*c*r)*((r^2)⁻¹*c⁻¹) := by rw [hrinv]; group
      _ = (c^2)⁻¹*(r^2)⁻¹ := by rw [hs,hmove]; group
  exact he ▸ Z.mul_mem (Z.inv_mem hc) (Z.inv_mem hr)

public theorem inf_centralizer_le_of_central_eight
    {G : Type*} [Group G] [Finite G]
    (Q R V Z L : Subgroup G) [IsElementaryAbelian 2 V]
    (hRQ : R≤Q) (hVR : V≤R) (hRN : Q≤normalizer (R:Set G))
    (hVcard : Nat.card V=8) (hRcard : Nat.card R=32) (hQcard : Nat.card Q≤64)
    (hZV : Z≤V) (hZcard : Nat.card Z=2)
    (hZcentral : Q≤centralizer (Z:Set G))
    (hcomm : ⁅Q,V⁆≤Z) (hself : R⊓centralizer (V:Set G)=V)
    (hcenter : R⊓centralizer (R:Set G)=Z) (hderived : ⁅R,R⁆≤Z)
    (a : G) (haQ : a∈Q) (ha2 : a^2=1)
    (hLV : L≤V) (hLcard : Nat.card L=4)
    (hfixed : (Q⊓centralizer (V:Set G))⊓centralizer ({a}:Set G)=L)
    (hvalue : ∀c∈Q⊓centralizer (V:Set G),⁅a,c⁆∈L) :
    Q⊓centralizer ({a}:Set G)≤R := by
  classical
  have hQcases : Q=R ∨ Nat.card Q=64 := by
    obtain ⟨n,hn⟩ := Subgroup.card_dvd_of_le hRQ
    rw [hRcard] at hn
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hncase : n=1 ∨ n=2 := by omega
    rcases hncase with hone | htwo
    · left
      apply (eq_of_le_of_card_ge hRQ ?_).symm
      omega
    · right
      omega
  rcases hQcases with heq | hQ64
  · exact heq ▸ inf_le_left
  let C := Q⊓centralizer (V:Set G)
  have hCQ : C≤Q := inf_le_left
  have hVC : V≤C := le_inf (hVR.trans hRQ) (le_centralizer V)
  have hCR : C⊓R=V := by
    dsimp only [C]
    rw [inf_comm,←inf_assoc,inf_eq_left.mpr hRQ]
    exact hself
  have hCcard : Nat.card C=16 := card_inf_centralizer_eq_sixteen_of_index_two
    Q R V Z hRQ hVcard hRcard hQ64 hZV hZcard hcomm hZcentral hself
  have hCN : C≤normalizer (R:Set G) := hCQ.trans hRN
  have hgen : R⊔C=Q := by
    apply eq_of_le_of_card_ge (sup_le hRQ hCQ)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes R C hCN
    rw [inf_comm R C,hCR,hRcard,hCcard,hVcard] at hh
    rw [hQ64]
    omega
  have hfactor (x:G) (hx:x∈Q) : ∃r∈R,∃c∈C,r*c=x := by
    have hm : x∈(R:Set G)*(C:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left R C hCN,hgen]
      exact hx
    exact hm
  have hVindex : (V.subgroupOf C).index=2 := by
    have hh := (V.subgroupOf C).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv,hVcard,hCcard] at hh
    omega
  have hVN : Q≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_right.mpr
    (hcomm.trans hZV)
  have hcentralizerN : normalizer (V:Set G)≤normalizer (centralizer (V:Set G):Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V:Set G))).mp inferInstance
  have hCRcomm : ⁅C,R⁆≤V := by
    rw [←hCR]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact commutator_le.mpr (fun c hc r hr =>
        Q.mul_mem (Q.mul_mem (Q.mul_mem (hCQ hc) (hRQ hr)) (Q.inv_mem (hCQ hc)))
          (Q.inv_mem (hRQ hr)))
    · exact le_normalizer_iff_commutator_le_left.mp
        (hRQ.trans (hVN.trans hcentralizerN)) |>.trans' (commutator_mono inf_le_right le_rfl)
    · exact le_normalizer_iff_commutator_le_right.mp hCN
  have hCsquare (c:G) (hc:c∈C) : c^2∈Z := by
    have hcV : c^2∈V := sq_mem_of_index_two hVindex (⟨c,hc⟩:C)
    apply hcenter.le
    refine ⟨hVR hcV,mem_centralizer_iff.mpr ?_⟩
    intro r hr
    have hcrV : ⁅c,r⁆∈V := hCRcomm (commutator_mem_commutator hc hr)
    have hccomm : c*⁅c,r⁆=⁅c,r⁆*c := (mem_centralizer_iff.mp hc.2 _ hcrV).symm
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=V) ⁅c,r⁆ hcrV
    have hz : ⁅c^2,r⁆=1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hccomm,mul_inv_cancel_right,←pow_two]
      exact hpow
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  have hRsquare (r:G) (hr:r∈R) : r^2∈Z := by
    apply hcenter.le
    refine ⟨R.pow_mem hr 2,mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have hrsZ := hderived (commutator_mem_commutator hr hs)
    have hrrs : r*⁅r,s⁆=⁅r,s⁆*r := (mem_centralizer_iff.mp (hZcentral (hRQ hr)) _ hrsZ).symm
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=V) ⁅r,s⁆ (hZV hrsZ)
    have hz : ⁅r^2,s⁆=1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hrrs,mul_inv_cancel_right,←pow_two]
      exact hpow
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  have hLC : L≤C := hLV.trans hVC
  have hZL : Z≤L := by
    intro z hz
    apply hfixed.le
    refine ⟨hVC (hZV hz),mem_centralizer_singleton_iff.mpr ?_⟩
    exact mem_centralizer_iff.mp (hZcentral haQ) z hz
  let f : C→*L := {
    toFun := fun c => ⟨⁅a,(c:G)⁆,hvalue c c.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro c d
      apply Subtype.ext
      change ⁅a,(c:G)*(d:G)⁆=⁅a,(c:G)⁆*⁅a,(d:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh := (mem_centralizer_iff.mp c.property.2 _ (hLV (hvalue d d.property))).symm
      calc
        _ = ⁅a,(c:G)⁆*((c:G)*⁅a,(d:G)⁆)*(c:G)⁻¹ := by group
        _ = _ := by rw [hh]; group }
  have hker : f.ker=L.subgroupOf C := by
    ext c
    change (⟨⁅a,(c:G)⁆,hvalue c c.property⟩:L)=1 ↔ (c:G)∈L
    rw [Subtype.ext_iff]
    change ⁅a,(c:G)⁆=1 ↔ (c:G)∈L
    rw [commutatorElement_eq_one_iff_mul_comm]
    constructor
    · intro hc
      exact hfixed.le ⟨c.property,mem_centralizer_singleton_iff.mpr hc.symm⟩
    · intro hc
      exact (mem_centralizer_singleton_iff.mp (hfixed.ge hc).2).symm
  have himage : f.range=⊤ := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hker,Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv,hLcard,hCcard] at hh
    apply eq_top_of_card_eq
    omega
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp himage
  let D := (Z.subgroupOf L).comap f
  have hDindex : D.index=2 := by
    rw [show D.index=(Z.subgroupOf L).index from index_comap_of_surjective (Z.subgroupOf L) hsurj]
    have hh := (Z.subgroupOf L).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZL).toEquiv,hZcard,hLcard] at hh
    omega
  have hVD : V.subgroupOf C≤D := by
    intro v hv
    exact hcomm (commutator_mem_commutator haQ hv)
  have hDeq : D=V.subgroupOf C := by
    apply (eq_of_le_of_card_ge hVD ?_).symm
    have hh := D.index_mul_card
    rw [hDindex,hCcard] at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv,hVcard]
    omega
  have hdetect (c:G) (hc:c∈C) : ⁅a,c⁆∈Z ↔ c∈V := by
    change (⟨c,hc⟩:C)∈D ↔ _
    rw [hDeq]
    rfl
  have haR : a∈R := by
    obtain ⟨r,hr,c,hc,heq⟩ := hfactor a haQ
    have hbracket : ⁅a,c⁆∈Z := by
      rw [←heq]
      exact square_product_commutator_mem Z r c (hRsquare r hr) (hCsquare c hc)
        (fun z hz => mem_centralizer_iff.mp (hZcentral (hCQ hc)) z hz)
        (heq ▸ ha2)
    exact heq ▸ R.mul_mem hr (hVR ((hdetect c hc).mp hbracket))
  intro x hx
  obtain ⟨r,hr,c,hc,heq⟩ := hfactor x hx.1
  have hbracket : ⁅a,c⁆∈Z := by
    have hzero : ⁅a,r*c⁆=1 := by
      rw [heq]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_singleton_iff.mp hx.2).symm
    have har : ⁅a,r⁆∈Z := hderived (commutator_mem_commutator haR hr)
    have hz : ⁅a,c⁆=⁅a,r⁆⁻¹ := by
      have hh : r*⁅a,c⁆*r⁻¹=⁅a,r⁆⁻¹ := by
        have he : ⁅a,r⁆*(r*⁅a,c⁆*r⁻¹)=1 := by
          simpa only [commutatorElement_mul_right_eq_mul_conj,mul_assoc] using hzero
        have hm := congrArg (fun y:G => ⁅a,r⁆⁻¹*y) he
        simpa only [inv_mul_cancel_left,mul_one] using hm
      have hcommute := mem_centralizer_iff.mp (hZcentral (hRQ (R.inv_mem hr))) _ (Z.inv_mem har)
      calc
        ⁅a,c⁆ = r⁻¹*(r*⁅a,c⁆*r⁻¹)*r := by group
        _ = r⁻¹*⁅a,r⁆⁻¹*r := by rw [hh]
        _ = ⁅a,r⁆⁻¹ := by rw [←hcommute]; group
    exact hz ▸ Z.inv_mem har
  exact heq ▸ R.mul_mem hr (hVR ((hdetect c hc).mp hbracket))
end Subgroup
