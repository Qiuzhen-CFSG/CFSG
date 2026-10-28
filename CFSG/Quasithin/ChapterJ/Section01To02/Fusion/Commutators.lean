module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientMaps
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.NaturalHead
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.CentralDecomposition
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry
public import Theory.GroupTheory.QuaternionCentralSupplement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The central decomposition and all three conclusions of J.2.4

From the genuine LocalSetup and the earlier quaternion conclusion
C_Q(B) ≃ Q₈ of J.2.3(7), this module proves CentralProductData and SourceJ24.
The marked natural section constructs HC = C_Q(B)U with intersection Z.
The cubic action on R₁/S, its index four and the literal fixed subgroup
C_{S/V}(R₁) = U/V then force the full commutator image modulo Z.

Given HC = C_Q(B)U with intersection Z and the full commutator image
modulo Z, the quaternion factor supplies Z ≤ [h,Q], so the actual H/Z
map lifts the image equality to [h,Q] = U. The commutator row Q → H/Z
has image of order 16 and kernel of order 128. The quaternion decomposition
puts HC in this kernel and gives |HC| = 128, proving C_Q(h) ≤ HC.
The centralizer calculation in the quaternion product then yields ⟨h⟩U.

The final assembly discharges the natural-section, fixed-subgroup, center,
residual and commutator premises using the proved earlier-source results.
Only the actual quaternion isomorphism from J.2.3(7) remains explicit;
its producer is `qt-j12-special-core`, with final source discharge owned by
`qt-j-01-02`. Neither the decomposition nor a commutator or centralizer
conclusion is assumed by `sourceJ24_of_quaternion`.

Source: Aschbacher–Smith, Lemma J.2.4, printed p.434 (PDF p.445).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Fusion
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The full image modulo Z, together with the quaternion decomposition,
implies the two remaining assertions of J.2.4. The other premises are
literal J.2.1–2 conclusions; no centralizer premise is needed. -/
theorem sourceJ24_of_centralProduct_of_modZ (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (cp : CentralProductData d B)
    (hZ : Nat.card d.Z = 2) (hQK : d.Q ≤ d.K)
    (hCK : ⁅d.HC,d.K⁆ ≤ d.U) (hUQ : ⁅d.U,d.Q⁆ ≤ d.Z)
    (hfull : ∀ h : G, ∀ hh : h ∈ d.HC, h ∉ d.U →
      ⁅zpowers (centerQuotientMap d ⟨h,hh.1⟩),modZ d d.Q⁆ = modZ d d.U) :
    SourceJ24 d := by
  let := d.elementary_U_of_card_Z hZ
  have hUHC : d.U ≤ d.HC := by rw [cp.product_eq]; exact le_sup_right
  have hBHC : HB d B ≤ d.HC := by rw [cp.product_eq]; exact le_sup_left
  have hBQ : HB d B ≤ d.Q := inf_le_left
  have hHCQ : d.HC ≤ d.Q := by
    rw [cp.product_eq]
    exact sup_le hBQ d.ru2.six.kernel_le
  have hCQ : ⁅d.HC,d.Q⁆ ≤ d.U := (commutator_mono le_rfl hQK).trans hCK
  have hinter : Nat.card (HB d B ⊓ d.U : Subgroup G) = 2 := by
    rw [cp.intersection_eq, hZ]
  have hBU : HB d B ≤ centralizer (d.U : Set G) := hBHC.trans inf_le_right
  obtain ⟨e⟩ := cp.quaternion
  have hHCcard : Nat.card d.HC = 128 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (HB d B) d.U
      ((le_centralizer_iff.mp hBU).trans (Subgroup.centralizer_le_normalizer _))
    have hb : Nat.card (HB d B) = 8 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide
    rw [hb, d.ru2.card_U hZ, hinter, ← cp.product_eq] at hh
    omega
  intro h hh hn
  have hhprod : h ∈ HB d B ⊔ d.U := cp.product_eq ▸ hh
  have hBcomm : ⁅zpowers h,HB d B⁆ = d.Z :=
    (commutator_quaternion_product (HB d B) d.U e hinter hBU hhprod hn).trans
      cp.intersection_eq
  have hcomm : ⁅zpowers h,d.Q⁆ ≤ d.U :=
    (commutator_mono (zpowers_le.mpr hh) le_rfl).trans hCQ
  have hZW : d.Z ≤ ⁅zpowers h,d.Q⁆ := by
    rw [← hBcomm]
    exact commutator_mono le_rfl hBQ
  have hfullh := hfull h hh hn
  have hlift : ⁅zpowers h,d.Q⁆ = d.U := by
    apply eq_of_modZ_eq d (hcomm.trans d.ru2.natural.section_le)
      d.ru2.natural.section_le hZW d.ru2.natural.kernel_le
    rw [modZ_commutator d (zpowers_le.mpr hh.1) (pCoreIn_le 2 d.H),
      modZ_zpowers d ⟨h,hh.1⟩]
    exact hfullh
  let f := commutatorRow d hUHC hCQ hUQ ⟨h,hh⟩
  have hfrange : f.range = modZ d d.U :=
    (commutatorRow_range d hUHC hCQ hUQ ⟨h,hh⟩).trans hfullh
  have hkerCard : Nat.card f.ker = 128 := by
    have hc := f.ker.index_mul_card
    rw [index_ker, hfrange, card_modZ_U d hZ, d.ru2.card_Q hZ] at hc
    omega
  have hHCker : d.HC.subgroupOf d.Q ≤ f.ker := by
    intro q hq
    have hp : (q : G) ∈ (↑(HB d B) : Set G) * (↑d.U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right (HB d B) d.U
        (hBU.trans (Subgroup.centralizer_le_normalizer _)), ← cp.product_eq]
      exact hq
    obtain ⟨b,hb,u,hu,he⟩ := hp
    have hqeq : q = (⟨b,hBQ hb⟩ : d.Q) * ⟨u,d.ru2.six.kernel_le hu⟩ := Subtype.ext he.symm
    change f q = 1
    rw [hqeq, map_mul]
    have hfb : f ⟨b,hBQ hb⟩ = 1 := by
      rw [commutatorRow_apply]
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅h,b⁆ ∈ d.Z
      rw [← hBcomm]
      exact commutator_mem_commutator (mem_zpowers _) hb
    have hfu : f ⟨u,d.ru2.six.kernel_le hu⟩ = 1 := by
      rw [commutatorRow_apply]
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅h,u⁆ ∈ d.Z
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hh.2 u hu).symm]
      exact d.Z.one_mem
    rw [hfb,hfu,mul_one]
  have hkerEq : d.HC.subgroupOf d.Q = f.ker := by
    apply eq_of_le_of_card_ge hHCker
    rw [hkerCard, Nat.card_congr (subgroupOfEquivOfLe hHCQ).toEquiv, hHCcard]
  have hcentralizer : d.Q ⊓ centralizer ({h} : Set G) ≤ d.HC := by
    intro q hq
    have hqker : (⟨q,hq.1⟩ : d.Q) ∈ f.ker := by
      change f ⟨q,hq.1⟩ = 1
      rw [commutatorRow_apply]
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅h,q⁆ ∈ d.Z
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_singleton_iff.mp hq.2).symm]
      exact d.Z.one_mem
    rw [← hkerEq] at hqker
    exact hqker
  refine ⟨hfullh, hlift, ?_⟩
  have he : d.Q ⊓ centralizer ({h} : Set G) = d.HC ⊓ centralizer ({h} : Set G) :=
    le_antisymm (le_inf hcentralizer inf_le_right) (inf_le_inf_right _ hHCQ)
  rw [he, cp.product_eq]
  exact centralizer_quaternion_product (HB d B) d.U e hinter hBU hhprod hn

/-- The central decomposition of J.2.4 from LocalSetup and the literal
earlier J.2.3(7) conclusion. Its natural-section premise is discharged. -/
theorem centralProductData_of_quaternion (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2)) :
    CentralProductData d.toTypeRuSetup B :=
  centralProductData_of_naturalHead d B d.fusionNaturalHead hq

/-- All three J.2.4 conclusions from LocalSetup and the earlier quaternion
isomorphism J.2.3(7). The decomposition, cubic action, quotient image and
centralizer calculation are proved; the fixed-subgroup input is discharged
by the actual J.2.3(8) Steinberg calculation. -/
theorem sourceJ24_of_quaternion (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2)) :
    SourceJ24 d.toTypeRuSetup := by
  have cp := centralProductData_of_quaternion d B hq
  have hCK : ⁅d.toTypeRuSetup.HC,d.toTypeRuSetup.K⁆ ≤ d.toTypeRuSetup.U := by
    rw [commutator_comm]
    exact commutator_le.mpr fun k hk c hc => d.HC_commutator_K_mem_U ⟨c,hc⟩ ⟨k,hk⟩
  have hUQ : ⁅d.toTypeRuSetup.U,d.toTypeRuSetup.Q⁆ ≤ d.toTypeRuSetup.Z := by
    rw [commutator_comm]
    exact d.toTypeRuSetup.commutator_Q_U_le_Z
  apply sourceJ24_of_centralProduct_of_modZ d.toTypeRuSetup B cp d.card_Z d.Q_le_K hCK hUQ
  apply modZ_commutator_eq_of_centralProduct d B cp
  have hcore : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2 := by
    rw [← d.parabolic_core_eq_R₁, ← d.H_inf_L, inf_comm]
  intro s hs hcomm
  exact (SpecialCore.CommutatorGeometry.mem_U_iff_commutators d hcore ⟨s,hs⟩).mpr hcomm

end CFSG.Quasithin.ChapterJ.Fusion
