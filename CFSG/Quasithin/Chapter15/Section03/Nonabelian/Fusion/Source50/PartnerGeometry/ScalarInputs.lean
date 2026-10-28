module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Multiplicity

/-!
# The literal source-56 dimension

The original extraspecial group has order 2^(2s+5), with its marked central
line of order two. Its actual binary quotient therefore has dimension
2(s+2), for the same canonical module multiplicity as source54.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

theorem vector_dimension_of_closure_card (s : ℕ)
    (hZ : Z ≤ closureU Z ZS) (hZcard : Nat.card Z = 2)
    (hU : Nat.card (closureU Z ZS)=2^(2*s+5)) :
    Module.finrank (ZMod 2) (Space Z ZS)=2*(s+2) := by
  have hcZ : Nat.card (Z.subgroupOf (closureU Z ZS))=2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv).trans hZcard
  have hQ := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf (closureU Z ZS))
  rw [hcZ,hU] at hQ
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space Z ZS)
  have hc : Nat.card (VectorQuotient Z ZS)=2^Module.finrank (ZMod 2) (Space Z ZS) :=
    (Nat.card_congr (Additive.toMul : Space Z ZS ≃ VectorQuotient Z ZS)).symm.trans
      (by simpa only [Nat.card_zmod] using hd)
  rw [hc, ← pow_succ] at hQ
  have he := Nat.pow_right_injective (by decide : 1<2) hQ
  omega

open CFSG.Quasithin.ChapterG.Section02
open OrthogonalPlusFour Chapter15Collapse
variable {Z ZS} {Zperp V Y T : Subgroup G} {g : G}

theorem literal_vector_dimension
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity) :
    Module.finrank (ZMod 2) (Space Z ZS)=2*(f.decomposition.leftMultiplicity+2) := by
  apply vector_dimension_of_closure_card Z ZS _ _ d.point_card
    (literal_closure_card hZS hperp hspan d hΩ f hsame)
  exact (show Z ≤ Zperp from d.base.point_le).trans hperp

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
