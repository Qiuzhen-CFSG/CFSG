module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerQuotient
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCentralizer
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The full M22 point-residual quotient

The original hexad map with its two-group kernel identifies the full
point-residual quotient by its two-core with A₆. The literal projection
into C_G(z)/O₂(C_G(z)) preserves this quotient. The source core product
O₂(L_z)=O₂(C_G(z))V and its intersection with V then give order 32 for
the two-core of that image, using the original orders 1024 and 32.

The calculation retains both original quotient maps and their kernels.
It needs no extraspecial marking or order of the centralizer core.
The earlier source block and normal-closure arguments must supply the
two-kernel, core product and intersection inputs.
Source: Aschbacher--Smith 8.2.10--13, printed pp.721--723,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Centralizer Chapter7.NormalizedSource.MathieuSextet
variable {G : Type*} [Group G] [Finite G]

/-- The entire point-residual quotient is A₆ once the original hexad map
has a two-group kernel. The literal centralizer projection preserves it. -/
theorem m22_point_residual_full_quotients
    (L : Subgroup G) (z : G) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (f : (L ⊓ centralizer ({z} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
      alternatingGroup (Fin 6)) ∧
    Nonempty ((pointResidualImage L z ⧸ pCore 2 (pointResidualImage L z)) ≃*
      alternatingGroup (Fin 6)) := by
  let C := L ⊓ centralizer ({z} : Set G)
  let S := MulAction.stabilizer M22 B
  let : Group.IsPerfect S := m22HexadStabilizer_isPerfect hB
  let eS : solvableResidual S ≃* S :=
    (MulEquiv.subgroupCongr (solvableResidual_eq_top (G := S))).trans topEquiv
  let eR : solvableResidual C ≃* localResidual L z :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let e : (localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
      alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
      ((f.solvableResidualMap.pCoreQuotientEquiv
        (f.solvableResidualMap_surjective hf) (f.solvableResidualMap_ker_isPGroup hk)).trans
        ((QuotientGroup.congr _ _ eS (pCore_map_iso 2 eS)).trans
          (MathieuCode.NormalizedShadowRows.code_hexad_core_equiv hB)))
  exact ⟨⟨e⟩,⟨((pointResidualProjection L z).pCoreQuotientEquiv
    (pointResidualProjection_surjective L z)
    (pointResidualProjection_kernel_isTwoGroup L z)).symm.trans e⟩⟩

/-- The source core product and intersection compute the core of the literal
point-residual image. No order or extraspecial marking of the ambient core
is needed for this calculation. -/
theorem m22_point_residual_image_core_card
    (L V : Subgroup G) (z : G)
    (hVC : V ≤ centralizer ({z} : Set G))
    (hproduct : localTwoCore L z = (centralizer ({z} : Set G)).pCoreIn 2 ⊔ V)
    (hcard : Nat.card V = 1024)
    (hcap : Nat.card ((centralizer ({z} : Set G)).pCoreIn 2 ⊓ V : Subgroup G) = 32) :
    Nat.card (pCore 2 (pointResidualImage L z)) = 32 := by
  let C := centralizer ({z} : Set G)
  let E := C.pCoreIn 2
  let R := localResidual L z
  let f := pointResidualProjection L z
  have hER : E ≤ R := (le_sup_left.trans hproduct.ge).trans (localTwoCore_le L z)
  have hker : Nat.card f.ker = Nat.card E := by
    rw [pointResidualProjection_kernel]
    exact Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv
  have hcore : Nat.card (pCore 2 R) = Nat.card (E ⊔ V : Subgroup G) := by
    have he := Nat.card_congr ((pCore 2 R).equivMapOfInjective
      R.subtype R.subtype_injective).toEquiv
    change Nat.card (pCore 2 R) = Nat.card (localTwoCore L z) at he
    rwa [hproduct] at he
  have hcount := f.card_pCore_of_ker_isPGroup
    (pointResidualProjection_surjective L z) (pointResidualProjection_kernel_isTwoGroup L z)
  rw [hker,hcore] at hcount
  have hnorm : V ≤ normalizer (E : Set G) := by
    have hn := (pCore 2 C).le_normalizer_map C.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hn
    exact hVC.trans hn
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes E V hnorm
  rw [hcard,hcap,hcount] at hmul
  have hpos : 0 < Nat.card E := Nat.card_pos
  nlinarith

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
