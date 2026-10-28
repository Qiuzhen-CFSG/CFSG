module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Factors
public import Theory.ElementaryAbelian.Quotient

/-!
# The actual central quotient of the marked wreath core

The diagonal central involution defines a literal quotient map on the Sylow.
The image of Q is elementary of order sixteen; the quotient equality and
commutation criteria retain the original wreath elements.

Source: Aschbacher–Smith 13.9.6, printed p.971 (PDF p.988).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm

def centralLine : Subgroup P := zpowers centralInP

theorem centralLine_le_center : centralLine ≤ center P :=
  zpowers_le.mpr (mem_center_iff.mpr centralInP_central)

instance centralLine_normal : centralLine.Normal := ⟨fun x hx g=>by
  rw [mem_center_iff.mp (centralLine_le_center hx) g,mul_inv_cancel_right]
  exact hx⟩

theorem centralInP_order : orderOf centralInP = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using centralInP_sq) centralInP_ne_one

theorem mem_centralLine (x : P) : x∈centralLine ↔ x=1 ∨ x=centralInP := by
  rw [centralLine,mem_zpowers_iff_mem_range_orderOf,centralInP_order]
  constructor
  · intro hw
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hw
    have hnlt : n<2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl|rfl)
    · exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩
    · exact Finset.mem_image.mpr ⟨1,by simp,by simp⟩

theorem card_centralLine : Nat.card centralLine = 2 := by
  rw [centralLine,Nat.card_zpowers,centralInP_order]

abbrev CentralQuotient := P ⧸ centralLine

def centralProjection : P →* CentralQuotient := QuotientGroup.mk' centralLine

def quotientCore : Subgroup CentralQuotient := coreInP.map centralProjection

private theorem coreProjection_ker : (centralProjection.comp coreInP.subtype).ker = center coreInP := by
  ext x
  change ((x:P) : P ⧸ centralLine)=1 ↔ x∈center coreInP
  rw [QuotientGroup.eq_one_iff]
  change (x:P)∈zpowers centralInP ↔ _
  rw [←center_coreInP]
  constructor
  · rintro ⟨a,ha,he⟩
    have heq : a=x := Subtype.ext he
    exact heq ▸ ha
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem card_quotientCore : Nat.card quotientCore = 16 := by
  have hr : (centralProjection.comp coreInP.subtype).range = quotientCore := by
    rw [MonoidHom.range_comp,range_subtype]
    rfl
  rw [←hr,←index_ker,coreProjection_ker,index_eq_card]
  exact coreInPQuaternionData.quotient_card

instance quotientCore_elementary : IsElementaryAbelian 2 quotientCore := by
  let f := centralProjection.comp coreInP.subtype
  let e : (coreInP ⧸ center coreInP) ≃* quotientCore :=
    (QuotientGroup.quotientMulEquivOfEq coreProjection_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype]; rfl)))
  let := coreInPQuaternionData.quotient_elementary
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

theorem centralProjection_eq (a b : P) :
    centralProjection a=centralProjection b ↔ a=b ∨ a=centralInP*b := by
  change (a : P ⧸ centralLine)=(b : P ⧸ centralLine) ↔ _
  rw [QuotientGroup.eq_iff_div_mem,mem_centralLine,div_eq_one,div_eq_iff_eq_mul]

theorem centralProjection_commute (a b : P) :
    Commute (centralProjection a) (centralProjection b) ↔
      a*b=b*a ∨ a*b=centralInP*(b*a) := by
  change centralProjection a*centralProjection b=centralProjection b*centralProjection a ↔ _
  rw [←map_mul,←map_mul,centralProjection_eq]
end SymmetricFourWreath
