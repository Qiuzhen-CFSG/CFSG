module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.CommutingGeometry.Automorphisms
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.CommutingGeometry.TwoOvergroup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.ProductIdentification
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction

/-!
# Commuting conjugates in the empty-family argument

The intrinsic displacement witness gives an actual L-conjugator of r.
Perfectness and the proved center/two-core equality show that the induced
action on L/O₂(L) is also an outer involution. The same intrinsic existence
theorem therefore supplies the quotient witness required by the quotient gap
argument. The precise earlier 16.1.6 alternative is retained explicitly for
each action. No fixed-point lifting or conjugacy-intersection conclusion is
assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1190, immediately after (+).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
open ComponentTransfer.Intrinsic CommutingGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
/-- A fixed involutory displacement gives the required actual commuting conjugate. -/
theorem commuting_conjugate_of_fixed_displacement
    (hn : r ∈ normalizer (L : Set G)) (hr2 : orderOf r = 2)
    (q : L) (hq : orderOf (action hn q * q⁻¹) = 2)
    (hf : action hn (action hn q * q⁻¹) = action hn q * q⁻¹) :
    MulAut.conj (q : G) r ≠ r ∧ Commute r (MulAut.conj (q : G) r) := by
  have hrr : r * r = 1 := by simpa only [pow_two, hr2] using pow_orderOf_eq_one r
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  let v : L := action hn q * q⁻¹
  have he : MulAut.conj (q : G) r = r * (v : G) := by
    change (q : G) * r * (q : G)⁻¹ = r * ((r * (q : G) * r⁻¹) * (q : G)⁻¹)
    rw [hri]
    calc
      (q : G) * r * (q : G)⁻¹ = (r * r) * ((q : G) * r * (q : G)⁻¹) := by rw [hrr, one_mul]
      _ = _ := by group
  have hrv : Commute r (v : G) := by
    have hh := congrArg Subtype.val hf
    change r * (v : G) * r⁻¹ = (v : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  constructor
  · intro hh
    have hv : v = 1 := Subtype.ext (mul_left_cancel (he.symm.trans (hh.trans (mul_one r).symm)))
    change orderOf v = 2 at hq
    simp [hv] at hq
  · rw [he]
    exact (Commute.refl r).mul_right hrv

/-- The commuting conjugate after (+), including the actual A₆ exception. -/
theorem exists_commuting_conjugate
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hearlier : SylowCentralizingAlternative (action (h.sylow_normalizes (h.le_sylow hr)))) :
    ∃ l ∈ L, MulAut.conj l r ≠ r ∧ Commute r (MulAut.conj l r) := by
  by_cases hnc : r ∉ centralizer (componentSylow T L : Set G)
  · exact exists_commuting_conjugate_of_noncentral_componentSylow h hr hr2 hnc
  · let hn := h.sylow_normalizes (h.le_sylow hr)
    obtain ⟨q, hq, hf⟩ := exists_fixed_displacement (action hn)
      (CoverFusion.action_order_two hn hr2 hout) (CoverFusion.action_not_inner hn hout) hearlier
    exact ⟨q, q.property, commuting_conjugate_of_fixed_displacement hn hr2 q hq hf⟩

/-- Outer involutory action survives the actual two-core quotient. -/
theorem quotientAction_outer_involution
    (heven : HasEvenTypeCentralizers G) (h : StandardSetup T z L)
    (hn : r ∈ normalizer (L : Set G)) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    orderOf (quotientAction hn) = 2 ∧ ¬ ∃ q, quotientAction hn = MulAut.conj q := by
  let : IsQuasisimple L := h.component.quasisimple
  have hc := heven.component_center_eq_twoCore h.involution h.component
  let e : (L ⧸ center L) ≃* (L ⧸ pCore 2 L) := QuotientGroup.quotientMulEquivOfEq hc
  have heq (x : L) : e (QuotientGroup.mk' (center L) x) = QuotientGroup.mk' (pCore 2 L) x :=
    QuotientGroup.quotientMulEquivOfEq_mk hc x
  have he : MulAut.centralQuotientAction e (action hn) = quotientAction hn := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    calc
      MulAut.centralQuotientAction e (action hn) (QuotientGroup.mk' (pCore 2 L) x) =
          MulAut.centralQuotientAction e (action hn) (e (QuotientGroup.mk' (center L) x)) :=
        congrArg _ (heq x).symm
      _ = e (QuotientGroup.mk' (center L) (action hn x)) :=
        MulAut.centralQuotientAction_apply e (action hn) x
      _ = QuotientGroup.mk' (pCore 2 L) (action hn x) := heq _
      _ = quotientAction hn (QuotientGroup.mk' (pCore 2 L) x) := (quotientAction_apply hn x).symm
  rw [← he]
  exact ⟨(orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans (CoverFusion.action_order_two hn hr2 hout),
    fun hi => CoverFusion.action_not_inner hn hout ((MulAut.centralQuotientAction_inner_iff e _).mp hi)⟩

/-- The intrinsic witness for the independent quotient-gap argument. -/
theorem exists_quotient_fixed_displacement
    (heven : HasEvenTypeCentralizers G) (h : StandardSetup T z L)
    (hn : r ∈ normalizer (L : Set G)) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hearlier : SylowCentralizingAlternative (quotientAction hn)) :
    ∃ q : L ⧸ pCore 2 L, orderOf (quotientAction hn q * q⁻¹) = 2 ∧
      quotientAction hn (quotientAction hn q * q⁻¹) = quotientAction hn q * q⁻¹ := by
  obtain ⟨ha, ho⟩ := quotientAction_outer_involution heven h hn hr2 hout
  exact exists_fixed_displacement (quotientAction hn) ha ho hearlier

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
