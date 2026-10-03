module

public import Stellmacher.SectionThree.ThreeNineSelectedFactorDichotomy

/-!
# The barred quotient dichotomy in Stellmacher (3.9)

This module exposes the source-facing quotient endpoint used by the final
assembly of Stellmacher (3.9).  In the faithful quotient
`H / C_H(V)`, the hypotheses say that both local residuals survive, both
local Baumann alternatives fail, and the image of the common Sylow subgroup
meets the quotient two-core trivially.  The conclusion is exactly the
remaining source dichotomy: either both ordered triple commutators vanish or
the two first commutators agree.

The substantive selected-factor, irreducibility, three-core, and action
transport argument is proved in `ThreeNineSelectedFactorDichotomy`; this
module is deliberately the thin stable wrapper consumed by
`LemmaThreeNine`.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.9), pp. 23--24; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

universe u

open BenderSuzuki.External

/-- The faithful-quotient dichotomy in the hard branch of Stellmacher (3.9). -/
public theorem threeNine_quotient_dichotomy
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hsolv₁ : Group.IsSolvable P₁) (hsolv₂ : Group.IsSolvable P₂)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (hsolv : Group.IsSolvable H)
    (hJ : elementaryAbelianMaxJ S =
      elementaryAbelianMaxJ (sylowAmbient T))
    (V C : Subgroup H)
    (hVdef : V = Subgroup.normalClosure
      ((omegaOneCenterAmbient S).subgroupOf H : Set H))
    (hVnormal : V.Normal) (hVelem : IsElementaryAbelian 2 V)
    (hCdef : C = Subgroup.centralizer (V : Set H)) (hCnormal : C.Normal)
    (hR₁C : ¬ twoResidualAmbient P₁ ≤ C.map H.subtype)
    (hR₂C : ¬ twoResidualAmbient P₂ ≤ C.map H.subtype)
    (hB₁ : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₁)
    (hB₂ : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₂)
    (hbarCore :
      letI : C.Normal := hCnormal
      let q : H →* H ⧸ C := QuotientGroup.mk' C
      (S.subgroupOf H).map q ⊓ pCore 2 (H ⧸ C) = ⊥) :
    ((⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆,
          twoResidualAmbient P₂⁆ = ⊥ ∧
      ⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆,
          twoResidualAmbient P₁⁆ = ⊥) ∨
      ⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆ =
        ⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆) := by
  exact threeNine_selected_factor_dichotomy S h P₁ P₂ H hP₁ hP₂ hH
    hsolv₁ hsolv₂ T hST hsolv hJ V C hVdef hVnormal hVelem hCdef
    hCnormal hR₁C hR₂C hB₁ hB₂ hbarCore

end Stellmacher.SectionThree
