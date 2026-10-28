module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Assembly
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.SourceApplications
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import Theory.GroupTheory.CentralizerPrimeKernel
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.CentralInvolutionFixedCore
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The center of the original HS overcomponent

Work inside the actual local extension L of the normal quasisimple component
X by a two-group. The involution t acts on X through the product-centralizer
class of HS, while i is the original central involution of L. The source
four-group bound puts C_{O₂(L)}(t) in ⟨t,i⟩. A component centralizes the two-core,
so t lies outside that core and its fixed subgroup is exactly ⟨i⟩. The source
nonfusion of t and ti then gives O₂(L)=⟨i⟩.

The proved HS odd-primary multiplier bound makes Z(X) a two-group, so a
nontrivial center would be exactly ⟨i⟩. Since both L/X and Z(X) are two-groups,
C_L(X) is a normal two-group and lies in X. Innerness of the literal action
therefore puts t in X. Its marked image is the non-two-central HS involution,
whose lifts have order four by I.2.2(5b), contradicting the original order two.
The universal B.4.8(2) input of that lifting theorem is discharged here.

The upper fixed-core bound and nonfusion are precisely the preceding source
R/Sylow and fusion steps retained by the Chapter 2 assembly. This argument
also applies to the smaller local extension X⟨t,i⟩.

Source: Aschbacher–Smith 2.5.19, printed pp.561–562, especially the HS paragraph
on p.562; applied to the original nonabelian-core branch of 2.5.21 on p.566.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HS
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
variable {L : Type*} [Group L] [Finite L]

private theorem center_eq_bot_of_core
    (X : Subgroup L) [X.Normal] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut X) (t i : L) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hact : ∀ x : X, (a x : L) = t * (x : L) * t⁻¹)
    (hmark : MulAut.congr e (quotientAut (center X) a) =
      MulAut.conj ClassCoverage.t)
    (hq : IsPGroup 2 (L ⧸ X)) (hcore : pCore 2 L = zpowers i) :
    center X = ⊥ := by
  by_contra hZne
  have hZp : IsPGroup 2 (center X) :=
    Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e
  have hZle : (center X).map X.subtype ≤ zpowers i := by
    rw [← hcore]
    exact le_sSup ⟨inferInstance, hZp.map X.subtype⟩
  have hZcard : Nat.card (center X) = 2 := by
    have hc : Nat.card (center X) ≤ 2 := by
      rw [← card_map_of_injective X.subtype_injective]
      simpa only [Nat.card_zpowers, hi] using card_le_of_le hZle
    have hn : Nat.card (center X) ≠ 1 := fun h => hZne (card_eq_one.mp h)
    have hp : 0 < Nat.card (center X) := Nat.card_pos
    omega
  have hZeq : (center X).map X.subtype = zpowers i := by
    apply eq_of_le_of_card_ge hZle
    rw [card_map_of_injective X.subtype_injective, hZcard, Nat.card_zpowers, hi]
  have hCX : centralizer (X : Set L) ≤ X := by
    have hc : centralizer (X : Set L) ≤ pCore 2 L :=
      le_sSup ⟨inferInstance, isPGroup_centralizer_of_quotient X hq hZp⟩
    rw [hcore, ← hZeq] at hc
    exact hc.trans (map_subtype_le _)
  have hain : ∃ x : X, a = MulAut.conj x := by
    apply (MulAut.centralQuotientAction_inner_iff e a).mp
    exact ⟨ClassCoverage.t, hmark⟩
  have ha : a = (MulAut.conjNormal t : MulAut X) := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hact x)
  have htX : t ∈ X := by
    have hm : t ∈ X ⊔ centralizer (X : Set L) := by
      rw [← MulAut.conjNormal_comap_innerSubgroup X]
      obtain ⟨x, hx⟩ := hain
      exact ⟨x, hx.symm.trans ha⟩
    rwa [sup_eq_left.mpr hCX] at hm
  let u : X := ⟨t, htX⟩
  have hau : a = MulAut.conj u := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hact x)
  have hm : HSLocal.modelMap e u = ClassCoverage.t := by
    apply MulAut.conj_injective_of_center_eq_bot Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
    change MulAut.conj (e (QuotientGroup.mk' (center X) u)) = _
    rw [← MulAut.centralQuotientAction_conj, ← hau]
    exact hmark
  have hu4 : orderOf u = 4 :=
    HSLocal.order_four_of_nonTwoCentral_image
      CFSG.Quasithin.ChapterB.NaturalExtensions.earlierB48Two e hZcard u
      (by rw [hm]; exact ClassCoverage.t_order)
      (by rw [hm]; exact HSLocal.t_not_twoCentral)
  have hu2 : orderOf u = 2 := (Subgroup.orderOf_coe u).symm.trans ht
  omega

private theorem fixed_core_eq_line
    (X : Subgroup L) [X.Normal] [IsQuasisimple X]
    (e : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut X) (t i : L) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hiZ : i ∈ center L)
    (hact : ∀ x : X, (a x : L) = t * (x : L) * t⁻¹)
    (hmark : MulAut.congr e (quotientAut (center X) a) =
      MulAut.conj ClassCoverage.t)
    (hbound : pCore 2 L ⊓ centralizer ({t} : Set L) ≤ zpowers t ⊔ zpowers i) :
    pCore 2 L ⊓ centralizer ({t} : Set L) = zpowers i := by
  classical
  have hlZ : zpowers i ≤ center L := zpowers_le.mpr hiZ
  let : (zpowers i).Normal := {
    conj_mem := by
      intro y hy g
      rw [mem_center_iff.mp (hlZ hy) g, mul_inv_cancel_right]
      exact hy }
  have hlp : IsPGroup 2 (zpowers i) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hi, pow_one])
  have hlQ : zpowers i ≤ pCore 2 L := le_sSup ⟨inferInstance, hlp⟩
  have ha1 : a ≠ 1 := by
    intro ha
    have hm : MulAut.conj ClassCoverage.t = MulAut.conj (1 : Sporadic.LeechRelated.HS.Carrier) := by
      calc
        MulAut.conj ClassCoverage.t = MulAut.centralQuotientAction e a := hmark.symm
        _ = 1 := by rw [ha, map_one]
        _ = MulAut.conj 1 := (map_one MulAut.conj).symm
    have ht1 := MulAut.conj_injective_of_center_eq_bot
      Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot hm
    have ho := ClassCoverage.t_order
    rw [ht1, orderOf_one] at ho
    omega
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  have hcomp : IsComponent L X :=
    ⟨(inferInstance : X.Normal).isSubnormal, inferInstance⟩
  have hXQ : X ≤ centralizer (pCore 2 L : Set L) :=
    hcomp.le_centralizer_of_solvable_normal (pCore 2 L)
  have htQ : t ∉ pCore 2 L := by
    intro htQ
    apply ha1
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a x : L) = (x : L)
    rw [hact x, hXQ x.property t htQ, mul_inv_cancel_right]
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_normal_right.mp (hbound hx)
    have huQ : u ∈ pCore 2 L := by
      exact ((pCore 2 L).mul_mem_cancel_right (hlQ hv)).mp hx.1
    rw [mem_zpowers_iff_mem_range_orderOf, ht] at hu
    obtain ⟨n, hn, hnEq⟩ := Finset.mem_image.mp hu
    have hn2 : n < 2 := Finset.mem_range.mp hn
    have hu1 : u = 1 := by
      interval_cases n
      · simpa only [pow_zero] using hnEq.symm
      · exact (htQ (by simpa only [← hnEq, pow_one] using huQ)).elim
    simpa only [hu1, one_mul] using hv
  · exact le_inf hlQ (fun x hx =>
      mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hlZ hx) t).symm)

/-- The original four-group bound and nonfusion force the HS overcomponent to
be centerless. The ordinary local quotient and marked action remain literal. -/
theorem center_eq_bot_of_fixed_core_bound
    (X : Subgroup L) [X.Normal] [IsQuasisimple X]
    (e : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut X) (t i : L) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hiZ : i ∈ center L)
    (hact : ∀ x : X, (a x : L) = t * (x : L) * t⁻¹)
    (hmark : MulAut.congr e (quotientAut (center X) a) =
      MulAut.conj ClassCoverage.t)
    (hq : IsPGroup 2 (L ⧸ X))
    (hbound : pCore 2 L ⊓ centralizer ({t} : Set L) ≤ zpowers t ⊔ zpowers i)
    (hnonfusion : ¬ IsConj t (t * i)) : center X = ⊥ := by
  have hfixed := fixed_core_eq_line X e a t i ht hi hiZ hact hmark hbound
  have hcore := eq_zpowers_of_fixed_central_involution_of_nonfusion (pCore 2 L)
    pCore_isPGroup t i (ht ▸ pow_orderOf_eq_one t) hi hiZ hfixed hnonfusion
  exact center_eq_bot_of_core X e a t i ht hi hact hmark hq hcore

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HS
