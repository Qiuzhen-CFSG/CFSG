module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Defs
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.ElementaryAbelian.Join

/-!
# The orthogonal layers in G.2.4

The actual A₅ action proves irreducibility of V_L. Its invariant two-core
therefore centralizes V_L. The Frattini bound from the proved G.2.2 and
the disjoint order-two points make U∩Uᵍ elementary abelian. The derived
bounds of U and Uᵍ give [U∩Uᵍ,I]≤V_L, so adjoining V_L gives the normal
second layer. It is a two-group, lies in O₂(I), and is elementary abelian
because the two factors centralize one another. The join is proved to be
the source's literal product.

Only L≤I, the consequence of G.2.4(2), remains explicit in clauses (4–5).
The source hypothesis supplies the full orthogonal action; no layer,
commutator, disjointness or centrality conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(4–5), printed pp.334–335, also used in 13.5.25, printed p.925.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

namespace Hypothesis
variable (d : Hypothesis D g)
include d

theorem VL_elementary : IsElementaryAbelian 2 D.VL := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact ⟨⟨fun x y => d.coordinates.injective (by simp [mul_comm])⟩⟩
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply d.coordinates.injective
    rw [map_pow, map_one, pow_two]
    change (d.coordinates x).toAdd + (d.coordinates x).toAdd = 0
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero ((d.coordinates x).toAdd.val i)

theorem irreducible (A : Subgroup G) (hA : A ≤ D.VL)
    (hn : D.L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = D.VL := by
  exact BinaryPermutation.invariant_subgroup_of_fiveCore D.VL
    ((MulAut.conj : G →* MulAut G).comp D.L.subtype)
    (fun l v hv => (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp hv)
    (d.model.toMonoidHom.comp (starProjection D))
    (d.model.surjective.comp (starProjection_surjective D)) d.coordinates
    d.equivariant A hA
    (fun l v hv => (mem_normalizer_iff.mp (hn l.property) v).mp hv)

theorem T_normalizes_VL : D.T ≤ normalizer (D.VL : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq]
  change (conjugateSpanBy D.V₁ D.L).map (MulAut.conj t).toMonoidHom = _
  have hpoint : D.V₁.map (MulAut.conj t).toMonoidHom = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (d.setup.T_normalizes_point ht)
  have hL : D.L.map (MulAut.conj t).toMonoidHom = D.L :=
    mem_normalizer_iff_map_conj_eq.mp (d.setup.T_normalizes_L ht)
  rw [map_conjugateSpanBy, hpoint, hL]
  rfl

theorem I_normalizes_VL : D.I g ≤ normalizer (D.VL : Set G) := by
  have hU := d.setup.U_normal_in_T.1.trans d.T_normalizes_VL
  apply sup_le hU
  rintro _ ⟨u, hu, rfl⟩
  change g⁻¹ * u * g⁻¹⁻¹ ∈ normalizer (D.VL : Set G)
  rw [inv_inv]
  exact (normalizer (D.VL : Set G)).mul_mem
    ((normalizer (D.VL : Set G)).mul_mem
      ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem)) (hU hu))
    (L_normalizes_VL D d.g_mem)

theorem points_disjoint : Disjoint D.V₁ (conjugate D.V₁ g) := by
  apply disjoint_iff.mpr
  apply inf_eq_bot_of_card_two_of_ne _ _ d.point_card
  · exact (card_map_of_injective (MulAut.conj g⁻¹).injective).trans d.point_card
  · intro he
    apply d.g_not_normalizes
    have hi : g⁻¹ ∈ D.G₁ := mem_normalizer_iff_map_conj_eq.mpr he.symm
    exact inv_inv g ▸ D.G₁.inv_mem hi

theorem intersection_elementary :
    IsElementaryAbelian 2 (D.U ⊓ conjugate D.U g : Subgroup G) :=
  conjugate_intersection_elementary d.setup.U_isPGroup d.setup.frattini_U_le_point
    g⁻¹ d.points_disjoint

theorem intersection_commutator : ⁅D.U ⊓ conjugate D.U g, D.I g⁆ ≤ D.VL := by
  have hd : ⁅D.U, D.U⁆ ≤ D.VL :=
    (derived_le_of_frattini_image_le d.setup.U_isPGroup d.setup.frattini_U_le_point).trans
      (le_conjugateSpanBy _ _)
  have hc : ⁅conjugate D.U g, conjugate D.U g⁆ ≤ D.VL := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hd
    have he : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))
    rw [map_commutator, he] at hm
    exact hm
  exact intersection_commutator_sup_le hd hc d.I_normalizes_VL

theorem VL_le_I (hLI : D.L ≤ D.I g) : D.VL ≤ D.I g :=
  conjugateSpanBy_le
    (d.setup.point_le.trans ((le_conjugateSpanBy _ _).trans le_sup_left))
    (hLI.trans (D.I g).le_normalizer)

theorem central_first (hLI : D.L ≤ D.I g) :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) := by
  let := d.VL_elementary
  have hp := IsElementaryAbelian.isPGroup 2 D.VL
  exact le_inf (le_pCoreIn_of_normalizes hp (d.VL_le_I hLI) d.I_normalizes_VL)
    (le_centralizer_iff.mp (pCoreIn_le_centralizer_of_irreducible D.VL D.L (D.I g)
      hp (d.VL_le_I hLI) d.I_normalizes_VL hLI d.irreducible))

theorem second_commutator (hLI : D.L ≤ D.I g) : ⁅S₂ D g, D.I g⁆ ≤ D.VL := by
  have hV := le_commutatorPreimage (d.VL_le_I hLI)
    (le_normalizer_iff_commutator_le_left.mp d.I_normalizes_VL)
  have hE := le_commutatorPreimage
    (show D.U ⊓ conjugate D.U g ≤ D.I g from inf_le_left.trans le_sup_left)
    d.intersection_commutator
  exact (commutator_mono (sup_le hV hE) le_rfl).trans
    (commutator_commutatorPreimage_le (D.I g) (D.I g) D.VL d.I_normalizes_VL)

theorem second_normal (hLI : D.L ≤ D.I g) : ((S₂ D g).subgroupOf (D.I g)).Normal := by
  have hEI : D.U ⊓ conjugate D.U g ≤ D.I g := inf_le_left.trans le_sup_left
  exact (normal_subgroupOf_iff_le_normalizer (sup_le (d.VL_le_I hLI) hEI)).mpr
    (le_normalizer_iff_commutator_le_left.mpr ((d.second_commutator hLI).trans le_sup_left))

theorem second_le_core (hLI : D.L ≤ D.I g) : S₂ D g ≤ D.S g := by
  have hEI : D.U ⊓ conjugate D.U g ≤ D.I g := inf_le_left.trans le_sup_left
  have hEV : D.U ⊓ conjugate D.U g ≤ normalizer (D.VL : Set G) :=
    hEI.trans d.I_normalizes_VL
  let := d.VL_elementary
  let := d.intersection_elementary
  have hp : IsPGroup 2 (S₂ D g) :=
    IsPGroup.to_sup_of_normal_left' (IsElementaryAbelian.isPGroup 2 D.VL)
      (IsElementaryAbelian.isPGroup 2 (D.U ⊓ conjugate D.U g : Subgroup G)) hEV
  exact le_pCoreIn_of_normalizes hp (sup_le (d.VL_le_I hLI) hEI)
    ((normal_subgroupOf_iff_le_normalizer (sup_le (d.VL_le_I hLI) hEI)).mp
      (d.second_normal hLI))

theorem second_elementary (hLI : D.L ≤ D.I g) : IsElementaryAbelian 2 (S₂ D g) := by
  let := d.VL_elementary
  let := d.intersection_elementary
  have hE : D.U ⊓ conjugate D.U g ≤ D.S g := le_sup_right.trans (d.second_le_core hLI)
  exact IsElementaryAbelian.sup_of_le_centralizer
    (hE.trans (le_centralizer_iff.mp ((d.central_first hLI).trans inf_le_right)))

theorem second_product (hLI : D.L ≤ D.I g) :
    (S₂ D g : Set G) = (D.VL : Set G) * (D.U ⊓ conjugate D.U g : Subgroup G) :=
  coe_mul_of_left_le_normalizer_right _ _
    ((d.central_first hLI).trans inf_le_right |>.trans
      (centralizer_le (show D.U ⊓ conjugate D.U g ≤ D.S g from
        le_sup_right.trans (d.second_le_core hLI))) |>.trans (Subgroup.centralizer_le_normalizer _))

/-- Relative normality in S, providing the actual quotient in clause (6). -/
theorem second_normal_in_core (hLI : D.L ≤ D.I g) :
    ((S₂ D g).subgroupOf (D.S g)).Normal := by
  have hnorm : D.I g ≤ normalizer (S₂ D g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((d.second_commutator hLI).trans le_sup_left)
  exact (normal_subgroupOf_iff_le_normalizer (d.second_le_core hLI)).mpr
    ((pCoreIn_le 2 (D.I g)).trans hnorm)

/-- The entire source layer conclusion, pending only the earlier generation
clause (2). The elementary second layer also feeds 13.5.25. -/
theorem orthogonal_layers (hLI : D.L ≤ D.I g) :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
    (D.VL.subgroupOf (D.I g)).Normal ∧
    ((S₂ D g).subgroupOf (D.I g)).Normal ∧
    ⁅S₂ D g, D.I g⁆ ≤ D.VL ∧ IsElementaryAbelian 2 (S₂ D g) :=
  ⟨d.central_first hLI, le_sup_left, d.second_le_core hLI,
    (normal_subgroupOf_iff_le_normalizer (d.VL_le_I hLI)).mpr d.I_normalizes_VL,
    d.second_normal hLI, d.second_commutator hLI, d.second_elementary hLI⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
