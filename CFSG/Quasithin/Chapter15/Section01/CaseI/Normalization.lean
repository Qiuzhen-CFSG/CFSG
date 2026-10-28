module
public import Theory.GroupTheory.PResidual.SylowNormalizer
public import Theory.GroupTheory.PResidual.SylowFactorIntersection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentData

/-!
# Case-I normalization of the marked centralizer

The source 15.1.18(3) argument first writes the two-residual of
`M_Z = C_G(Z₁) ∩ M_c` as the join of the two residual factors supplied by
the ordering factorization and 15.1.18(2).  Each factor is normalized by
the original Sylow group `T`.  Since `S = C_T(Z₁)` is a Sylow subgroup of
`M_Z` and is normal in `T`, the residual--Sylow supplement normalizes all of
`M_Z`.  This leaf proves that final transport from the literal source
factorization; the marked residual product and Sylow facts remain explicit
inputs from their source producers.

Source: Aschbacher--Smith 15.1.18(3), printed pp.1092--1093.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

theorem caseI_T_normalizes_MZ_of_residual_product
    {T H S R C : Subgroup G}
    (hproduct : (pResidual 2 H).map H.subtype = R ⊔ C)
    (hR : T ≤ normalizer (R : Set G))
    (hC : T ≤ normalizer (C : Set G))
    (hST : S ≤ T)
    (hSnT : (S.subgroupOf T).Normal)
    (hSyl : ∃ P : Sylow 2 H,
      (P : Subgroup H).map H.subtype = S) :
    T ≤ normalizer (H : Set G) := by
  exact Subgroup.le_normalizer_of_residual_sup_sylow T H S R C hproduct hR hC
    hST hSnT hSyl

/- The source ordering factorization itself produces the residual product.
   In particular, the product is not accepted as a normality callback: the
   Sylow-containing factor `A` and the residual containment of `C` are the
   only ordering inputs needed below. -/
theorem caseI_T_normalizes_MZ_of_ordering_factor
    (T : Sylow 2 G) {D A C H S R : Subgroup G}
    (hfactor : D = A ⊔ C)
    (hTA : (T : Subgroup G) ≤ A)
    (hDC : D ≤ normalizer (C : Set G))
    (hHD : H ≤ D)
    (hresC : (pResidual 2 C).map C.subtype ≤ H)
    (hresA : (pResidual 2 (A ⊓ H : Subgroup G)).map (A ⊓ H).subtype = R)
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hST : S ≤ (T : Subgroup G))
    (hSnT : (S.subgroupOf (T : Subgroup G)).Normal)
    (hSyl : ∃ P : Sylow 2 H,
      (P : Subgroup H).map H.subtype = S) :
    T ≤ normalizer (H : Set G) := by
  have hprod := embedded_pResidual_intersection_of_sylow_factor
    T D A C H hfactor hTA hDC hHD hresC
  rw [hresA] at hprod
  have hAD : A ≤ D := hfactor ▸ le_sup_left
  have hTC : (T : Subgroup G) ≤ normalizer
      ((pResidual 2 C).map C.subtype : Set G) :=
    (hTA.trans (hAD.trans hDC)).trans
      (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  exact caseI_T_normalizes_MZ_of_residual_product
    hprod hTR hTC hST hSnT hSyl

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply the literal residual-product argument to the original Case-I datum. -/
theorem T_normalizes_MZ_of_residual_product
    (d : CaseIComponentData T M Mc V) (R C : Subgroup G)
    (hproduct : (pResidual 2 d.MZ).map d.MZ.subtype = R ⊔ C)
    (hR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hSnT : (d.S.subgroupOf (T : Subgroup G)).Normal)
    (hSyl : ∃ P : Sylow 2 d.MZ,
      (P : Subgroup d.MZ).map d.MZ.subtype = d.S) :
    (T : Subgroup G) ≤ normalizer (d.MZ : Set G) := by
  exact caseI_T_normalizes_MZ_of_residual_product
    (T := (T : Subgroup G)) (H := d.MZ) (S := d.S) (R := R) (C := C)
    hproduct hR hC d.S_le_T hSnT hSyl

/-- The source 15.1.18(3) adapter from the literal ordering factorization. -/
theorem T_normalizes_MZ_of_ordering_factor
    (d : CaseIComponentData T M Mc V) (A C R : Subgroup G)
    (hfactor : Mc = A ⊔ C)
    (hTA : (T : Subgroup G) ≤ A)
    (hMC : Mc ≤ normalizer (C : Set G))
    (hMZ : d.MZ ≤ Mc)
    (hresC : (pResidual 2 C).map C.subtype ≤ d.MZ)
    (hresA : (pResidual 2 (A ⊓ d.MZ : Subgroup G)).map (A ⊓ d.MZ).subtype = R)
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hSnT : (d.S.subgroupOf (T : Subgroup G)).Normal)
    (hSyl : ∃ P : Sylow 2 d.MZ,
      (P : Subgroup d.MZ).map d.MZ.subtype = d.S) :
    (T : Subgroup G) ≤ normalizer (d.MZ : Set G) := by
  exact caseI_T_normalizes_MZ_of_ordering_factor
    T (D := Mc) (A := A) (C := C)
    (H := d.MZ) (S := d.S) (R := R) hfactor hTA hMC hMZ hresC hresA hTR
    d.S_le_T hSnT hSyl

/-- The marked two-core is normalized once `M_Z` is normalized. -/
theorem T_normalizes_Q1_of_T_normalizes_MZ (d : CaseIComponentData T M Mc V)
    (hTn : (T : Subgroup G) ≤ normalizer (d.MZ : Set G)) :
    (T : Subgroup G) ≤ normalizer (d.Q1 : Set G) := by
  exact hTn.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
