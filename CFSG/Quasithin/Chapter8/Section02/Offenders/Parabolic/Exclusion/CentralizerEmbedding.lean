module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Models
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Placement
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.MathieuExtension

/-!
# Centralizer placement and the marked terminal extension

The placement theorem constructs the containing component using the full
earlier appendix implications. Once A.3.18 identifies that component with
O^{3′}(C_G(z)), the source {2,3}-support gives X ≤ K. We restrict the ambient
Sylow subgroup to KT in the correct direction before applying the adequate
intrinsic Ξ theorem, retaining its Held alternative.

For a homomorphism from the original H into M₁₁ with the actual two-core
kernel and the marked permutable Sylow/complement image, the normal E₉
constructed in `MathieuExtension` pulls back to H/O₂(H). Its quotient is
the fixed SD₁₆ model, giving the parent's contradiction with H/O₂,₃(H) ≃ D₈.

The full A.3.12 comparison, A.3.18 model exclusions, the resulting M₁₁
identification, and construction of that marked homomorphism remain source
obligations. The conditional consumer below does not assert them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 8.2.2(1), printed p.715 (PDF p.732).
-/

public section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
open Subgroup Theory.GroupTheory Chapter1 Chapter1.XiEmbedding
open Sporadic.Mathieu
open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- The literal two-core quotient acquires a normal E₉ from a marked
homomorphism. Both the kernel and the image of that homomorphism are retained. -/
theorem marked_parabolic_extension (H : Subgroup G)
    (S : Sylow 2 M11) (R : Subgroup M11) (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11))
    (f : H →* M11) (hker : f.ker = pCore 2 H)
    (himage : f.range = R ⊔ (S : Subgroup M11)) :
    ∃ (N : Subgroup (H ⧸ pCore 2 H)) (_ : N.Normal),
      IsElementaryAbelian 3 N ∧ Nat.card N = 9 ∧
        Nonempty (((H ⧸ pCore 2 H) ⧸ N) ≃*
          Semidihedral.StandardModel 4 (by decide)) := by
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr himage))
  obtain ⟨N, hn, he, hc, -, hs⟩ := Mathieu.marked_extension S R hR hperm e
  exact ⟨N, hn, he, hc, hs⟩

/-- The reconstructed extension is applied to the original H and its
literal O₂,₃ quotient, using the parent's already proved incompatibility. -/
theorem incompatible_marked_parabolic (H : Subgroup G)
    (hD : Nonempty
      (H ⧸ (pCore 3 (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≃*
        DihedralGroup 4))
    (S : Sylow 2 M11) (R : Subgroup M11) (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11))
    (f : H →* M11) (hker : f.ker = pCore 2 H)
    (himage : f.range = R ⊔ (S : Subgroup M11)) : False := by
  obtain ⟨N, hn, he, -, hs⟩ := marked_parabolic_extension H S R hR hperm f hker himage
  let _ := hn
  let _ := he
  exact incompatible_parabolic_quotients H hD N (IsElementaryAbelian.isPGroup 3 N) hs

/-- Residual transfer and Sylow restriction supply the exact intrinsic
input inside KT. The use of `restrict` goes from C_G(z) down to KT. -/
theorem xi_input_in_component_join [Finite G]
    (T : Sylow 2 G) (H K : Subgroup G) (z : G)
    (hTH : (T : Subgroup G) ≤ H) (hHC : H ≤ centralizer ({z} : Set G))
    (hH : IsPiGroup twoThreePrimes H)
    (hK : (primeToResidual 3 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = K)
    (hX : (pResidual 2 H).map H.subtype ∈ Xi G T)
    (hq : XiOddQuotient 3 (XiQuotient ((pResidual 2 H).map H.subtype)))
    (P : Sylow 3 ((pResidual 2 H).map H.subtype)) :
    let X := (pResidual 2 H).map H.subtype
    X ≤ K ∧ IsSylowIn 2 T (K ⊔ (T : Subgroup G)) ∧
      LocalInput 3 T X ((P : Subgroup X).map X.subtype) (K ⊔ (T : Subgroup G)) := by
  let C := centralizer ({z} : Set G)
  have hTC : (T : Subgroup G) ≤ C := hTH.trans hHC
  have hKC : K ≤ C := hK ▸ map_subtype_le _
  have hTs : IsSylowIn 2 T C := ⟨T.subtype hTC, by
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTC]⟩
  have hTJ := hTs.restrict
    (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) (sup_le hKC hTC)
  have hXK := twoResidual_le_involution_component H K z hHC hH hK
  exact ⟨hXK, hTJ, localInput_of_mem_Xi hX hTJ
    (sup_le (hXK.trans le_sup_left) le_sup_right) (by decide) hq P⟩

/-- Source application of the adequate earlier Ξ implication. Held is
carried to the subsequent full appendix-list comparison. -/
theorem adequate_xi_in_component_join [Finite G] {κ : GroupClass.{u}}
    (hXi : EarlierAdequateXi κ)
    (T : Sylow 2 G) (H K : Subgroup G) (z : G)
    (hTH : (T : Subgroup G) ≤ H) (hHC : H ≤ centralizer ({z} : Set G))
    (hH : IsPiGroup twoThreePrimes H)
    (hK : (primeToResidual 3 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = K)
    (hX : (pResidual 2 H).map H.subtype ∈ Xi G T)
    (hq : XiOddQuotient 3 (XiQuotient ((pResidual 2 H).map H.subtype)))
    (hJ : IsSQTK κ (K ⊔ (T : Subgroup G) : Subgroup G))
    (P : Sylow 3 ((pResidual 2 H).map H.subtype)) :
    let X := (pResidual 2 H).map H.subtype
    AdequateXiConclusion T X ((P : Subgroup X).map X.subtype) (K ⊔ (T : Subgroup G)) := by
  obtain ⟨-, hT, hlocal⟩ := xi_input_in_component_join T H K z hTH hHC hH hK hX hq P
  exact hXi G _ _ _ _ hlocal hJ hT

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
