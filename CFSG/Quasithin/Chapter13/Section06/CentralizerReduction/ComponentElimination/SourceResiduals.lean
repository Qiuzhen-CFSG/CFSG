module

public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceThompson

/-!
# The actual residuals in the final orthogonal argument

Once 13.6.23(1) identifies K with O^{3′}(Gᵥ), residual intersection
gives O^{3′}(C_K(z)) = O^{3′}(C_{Gᵥ}(z)). The latter centralizer is
literally C_G(⟨z,v⟩). Thus normalization of the plane by T makes its
centralizer residual T-invariant. The proved Thompson argument then
uses this actual residual and the orthogonal model's J-comparison.

This proves the residual equalities and normalizer deductions, conditional
on 13.6.23(1) and the model comparison. It does not establish the component
classification or those two remaining premises. Every residual here is
O^{3′}; neither O³ nor O_{3′} occurs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.933,
concluding paragraph proving Theorem 13.6.7.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
variable {G : Type*} [Group G]

/-- The source X, using the prime-to-three residual of the relative
centralizer in K, embedded in the original ambient group. -/
def orthogonalResidual (K : Subgroup G) (z : G) : Subgroup G :=
  (primeToResidual 3 (K ⊓ Gv z : Subgroup G)).map (K ⊓ Gv z).subtype

/-- The common element centralizer is the centralizer of the generated
subgroup ⟨z,v⟩, with an explicit subgroup join. -/
theorem centralizer_plane_eq (z v : G) :
    centralizer ((zpowers z ⊔ zpowers v : Subgroup G) : Set G) = Gv v ⊓ Gv z := by
  have hz : centralizer (zpowers z : Set G) = Gv z := by
    rw [zpowers_eq_closure, centralizer_closure]
    rfl
  have hv : centralizer (zpowers v : Set G) = Gv v := by
    rw [zpowers_eq_closure, centralizer_closure]
    rfl
  apply le_antisymm
  · exact le_inf
      ((centralizer_le (show zpowers v ≤ zpowers z ⊔ zpowers v from le_sup_right)).trans hv.le)
      ((centralizer_le (show zpowers z ≤ zpowers z ⊔ zpowers v from le_sup_left)).trans hz.le)
  · apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_right.trans hz.ge)
    · exact le_centralizer_iff.mp (inf_le_left.trans hv.ge)

/-- The first residual equality follows from 13.6.23(1), with no further
orthogonal-module or centralizer-isomorphism premise. -/
theorem orthogonalResidual_eq_common_centralizer [Finite G]
    (K : Subgroup G) (z v : G)
    (hK : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype) :
    orthogonalResidual K z =
      (primeToResidual 3 (Gv v ⊓ Gv z : Subgroup G)).map (Gv v ⊓ Gv z).subtype := by
  rw [orthogonalResidual, hK]
  exact embedded_primeToResidual_intersection 3 (Gv v) (Gv z)

/-- The final equality uses the actual plane V₂ = ⟨z,v⟩. -/
theorem orthogonalResidual_eq_plane_centralizer [Finite G]
    (K V₂ : Subgroup G) (z v : G)
    (hK : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype)
    (hV₂ : V₂ = zpowers z ⊔ zpowers v) :
    orthogonalResidual K z =
      (primeToResidual 3 (centralizer (V₂ : Set G))).map
        (centralizer (V₂ : Set G)).subtype := by
  rw [hV₂, centralizer_plane_eq]
  exact orthogonalResidual_eq_common_centralizer K z v hK

/-- T-invariance of X is deduced from T-invariance of the source plane. -/
theorem normalizes_orthogonalResidual [Finite G]
    (K V₂ T : Subgroup G) (z v : G)
    (hK : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype)
    (hV₂ : V₂ = zpowers z ⊔ zpowers v)
    (hT : T ≤ normalizer (V₂ : Set G)) :
    T ≤ normalizer (orthogonalResidual K z : Set G) := by
  rw [orthogonalResidual_eq_plane_centralizer K V₂ z v hK hV₂]
  exact (hT.trans (normalizer_le_normalizer_centralizer V₂)).trans
    (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))

/-- Consumer of the source residual identity and the orthogonal Thompson
comparison. The residual's placement and T-invariance are proved here. -/
theorem false_of_residual_thompson_comparison [Finite G]
    (T : Sylow 2 G) (K V₂ : Subgroup G) (z v : G)
    (hK : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype)
    (hV₂ : V₂ = zpowers z ⊔ zpowers v)
    (hT : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hvT : v ∈ T) (hv : v ≠ 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hJ : elementaryAbelianMaxJ ((orthogonalResidual K z ⊔ Tv (T : Subgroup G) v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv (T : Subgroup G) v).pCoreIn 2))
    (h16 : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) : False := by
  have hKv : K ≤ Gv v := by
    rw [hK]
    exact map_subtype_le _
  exact false_of_orthogonal_thompson_comparison T v K (orthogonalResidual K z) hvT hv
    ((map_subtype_le _).trans (inf_le_left.trans hKv))
    (normalizes_orthogonalResidual K V₂ T z v hK hV₂ hT) hidx hJ h16

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
