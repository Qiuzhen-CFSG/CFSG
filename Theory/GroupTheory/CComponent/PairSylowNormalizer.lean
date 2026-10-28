module
public import Theory.GroupTheory.IndexTwoDihedralNormalizer
public import Theory.GroupTheory.CComponent.NormalPair
public import Theory.GroupTheory.CComponent.BinaryRankTwo
public import Theory.GroupTheory.AutomorphismSylowNormalizer

/-!
# Sylow normalizers in exchanged component pairs

If a normal supplement has self-normalizing Sylow two-subgroups, every
T-normal subgroup between T∩R and T has full normalizer T. For a pair of
C-components above the ambient two-core, self-normalization follows from
the direct product of their radical-free images and lifts through the
two-group kernel. The index-two component stabilizer then has normalizer T.

The source consumer retains the literal component and Sylow intersections
inside Mc. Source: the finite-group normalizer step in Aschbacher--Smith
14.6.24(1), printed p.1039, using component calculus A.3.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

/-- If a normal supplement has self-normalizing Sylows, the normalizer of
any T-normal subgroup between T∩R and T is T. -/
theorem normalizer_subgroup_eq_of_normal_supplement
    (T : Sylow 2 G) (R : Subgroup G) [R.Normal]
    (hgen : R ⊔ (T : Subgroup G) = ⊤)
    (hR : ∀ P : Sylow 2 R, normalizer (P : Set R) = P)
    (S : Subgroup G) (hST : S ≤ T) (hTR : (T : Subgroup G) ⊓ R ≤ S)
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G)) :
    normalizer (S : Set G) = T := by
  have he : S ⊓ R = (T : Subgroup G) ⊓ R :=
    le_antisymm (inf_le_inf_right R hST) (le_inf hTR inf_le_right)
  have hn : normalizer (S : Set G) ≤ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) := by
    rw [←he]
    exact (le_inf le_rfl le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have ht : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) :=
    (le_inf T.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal R
  have hr : R ⊓ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) ≤ T := by
    intro r hr
    have hp : (⟨r,hr.1⟩ : R) ∈ normalizer (P : Set R) := by
      rw [show (P : Set R) = ((T : Subgroup G).subgroupOf R : Set R) from congrArg SetLike.coe hP]
      have hi : ((T : Subgroup G) ⊓ R).subgroupOf R = (T : Subgroup G).subgroupOf R := by
        ext x
        exact and_iff_left x.property
      rw [←hi,←subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right)]
      exact hr.2
    rw [hR P] at hp
    change (⟨r,hr.1⟩ : R) ∈ (P : Subgroup R) at hp
    rw [hP] at hp
    exact hp
  apply le_antisymm ?_ hTS
  intro g hg
  have hgprod : g ∈ (R : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left R (T : Subgroup G) le_normalizer_of_normal,hgen]
    trivial
  obtain ⟨r,hrR,t,htT,rfl⟩ := hgprod
  have hrN : r ∈ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) := by
    simpa only [mul_inv_cancel_right] using
      (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).mul_mem (hn hg)
        ((normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).inv_mem (ht htT))
  exact (T : Subgroup G).mul_mem (hr ⟨hrR,hrN⟩) htT

/-- Two component quotients with self-normalizing Sylows give the same
property for their join above the ambient two-core. -/
theorem self_normalizing_cComponent_pair
    (hR : solvableRadical G = pCore 2 G)
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    {Q : Type*} [Group Q] [Finite Q]
    (a : (B ⧸ pCore 2 B) ≃* Q) (b : (C ⧸ pCore 2 C) ≃* Q)
    (hQ : ∀ P : Sylow 2 Q, normalizer (P : Set Q) = P)
    (P : Sylow 2 (B ⊔ C : Subgroup G)) : normalizer (P : Set (B ⊔ C : Subgroup G)) = P := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hrad : solvableRadical (G ⧸ pCore 2 G) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hBq := hB.map_quotient (pCore 2 G)
  have hCq := hC.map_quotient (pCore 2 G)
  have hneq : B.map q ≠ C.map q := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  have hc := hBq.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hrad hCq hneq
  obtain ⟨d,_⟩ := hBq.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hrad hc
  have aq : B.map q ≃* Q := (cComponentTwoCoreQuotientEquiv hB).symm.trans a
  have bq : C.map q ≃* Q := (cComponentTwoCoreQuotientEquiv hC).symm.trans b
  have f : ((B ⊔ C).map q) ≃* (Q × Q) :=
    (MulEquiv.subgroupCongr (map_sup B C q)).trans (d.symm.trans (aq.prodCongr bq))
  apply self_normalizing_of_two_kernel (q.subgroupMap (B ⊔ C))
    (q.subgroupMap_surjective (B ⊔ C)) ?_ ?_ P
  · rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  · exact self_normalizing_of_surjective f.symm.toMonoidHom f.symm.surjective
      (SylowNormalizerAction.product_sylow_self_normalizing hQ)

end Sylow

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The Sylow component stabilizer in an exchanged pair has no additional
normalizer when the simple factor has self-normalizing Sylows. -/
theorem IsCComponent.normalizer_sylow_component_eq_of_exchanged_pair
    (T : Sylow 2 G) (hR : solvableRadical G = pCore 2 G)
    {B : Subgroup G} (hB : B.IsCComponent)
    (t : G) (hne : B ≠ B.conjBy t) [(B ⊔ B.conjBy t).Normal]
    (hgen : (B ⊔ B.conjBy t) ⊔ (T : Subgroup G) = ⊤)
    {Q : Type*} [Group Q] [Finite Q]
    (a : (B ⧸ pCore 2 B) ≃* Q)
    (hQ : ∀ P : Sylow 2 Q, normalizer (P : Set Q) = P) :
    normalizer ((T : Subgroup G) ⊓ normalizer (B : Set G) : Set G) = T := by
  have hC : (B.conjBy t).IsCComponent := hB.map_equiv (MulAut.conj t)
  let b := (MulAut.conj t).subgroupMap B
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hself := Sylow.self_normalizing_cComponent_pair hR hB hC hne a (bq.symm.trans a) hQ
  let : (normalizer (B : Set G)).Normal := normal_of_index_eq_two
    (hB.normalizer_index_two_of_normal_pair t hne)
  apply T.normalizer_subgroup_eq_of_normal_supplement (B ⊔ B.conjBy t) hgen hself
    ((T : Subgroup G) ⊓ normalizer (B : Set G)) inf_le_left
  · exact le_inf inf_le_left (inf_le_right.trans
      ((sup_le (le_cComponentLayer hB) (le_cComponentLayer hC)).trans (cComponentLayer_le_normalizer hB)))
  · exact (le_inf T.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

end Subgroup
