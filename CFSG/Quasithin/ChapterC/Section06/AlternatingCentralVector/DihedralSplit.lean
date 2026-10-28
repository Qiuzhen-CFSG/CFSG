module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.ElementaryPair
public import Theory.GroupTheory.PGroup.ElementaryDihedralSplit
public import Theory.GroupTheory.DisjointCommutingProduct.Center


/-!
# The marked initial dihedral split in C.6.4

Choose u in U whose right conjugate by the actual escaping element x leaves
Q. If u commuted with this conjugate, the index-two generation of R would
make u central in R and hence make its conjugate central, a contradiction.
Their commutator is therefore the original two-element line. A binary
Jordan-plane complement gives R = E × ⟨u,uˣ⟩, with the latter isomorphic
to D₈ and E of index two in Z(R).

Source: Aschbacher–Smith C.6.4, printed p.168, immediately before the maximal
dihedral-overgroup argument. The x, u, line and factor embeddings are retained.
-/

public noncomputable section

open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- The source decomposition with its actual conjugate generators and central line. -/
theorem Input.exists_marked_dihedral_split (d : Input K R S Λ) :
    ∃ x ∈ Λ ⊓ normalizer (R : Set G), ∃ u ∈ (blockU K).map K.subtype,
    ∃ E D : Subgroup G, E ≤ (K ⊔ S).pCoreIn 2 ∧ IsElementaryAbelian 2 E ∧
      E ≤ centralizer (R : Set G) ∧ R = E ⊔ D ∧ Disjoint E D ∧
      D = zpowers u ⊔ zpowers (MulAut.conj x⁻¹ u) ∧
      Nonempty (D ≃* DihedralGroup 4) ∧
      D ⊓ centralizer (D : Set G) = ⁅(blockU K).map K.subtype,R⁆ ∧
      E.relIndex (R ⊓ centralizer (R : Set G)) = 2 := by
  let Q := (K ⊔ S).pCoreIn 2
  let U := (blockU K).map K.subtype
  let Z := ⁅U,R⁆
  obtain ⟨x,hx,hex,_,_,_,_,hE,_⟩ := d.exists_elementary_factorization
  let W := U.map (MulAut.conj x⁻¹).toMonoidHom
  let := hE
  let := d.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hRmap : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx.2)
  have hWR : W ≤ R := (map_mono (d.module_le_core.trans d.core_le)).trans_eq hRmap
  obtain ⟨r,hrW,hrQ⟩ := SetLike.not_le_iff_exists.mp hex
  obtain ⟨u,hu,hur⟩ := hrW
  change MulAut.conj x⁻¹ u = _ at hur
  let r := MulAut.conj x⁻¹ u
  have hrQ : r ∉ Q := by
    change MulAut.conj x⁻¹ u ∉ Q
    rwa [hur]
  have hrW : r ∈ W := mem_map_of_mem _ hu
  have hrR : r ∈ R := hWR hrW
  have hr2 : r ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := W) r hrW
  have hi : Q.relIndex R = 2 := by
    let := d.core_normal_in_R
    let := d.quotient_elementary_rank_one.1
    rw [c6_3_order_of_elementary_quotient,d.quotient_elementary_rank_one.2]
    rfl
  have hgen := sup_zpowers_eq_of_relIndex_prime d.core_le Nat.prime_two hi hrR hrQ
  have hz1 : ⁅r,u⁆ ≠ 1 := by
    intro hh
    have huc : u ∈ centralizer (R : Set G) := by
      have hRQ : R ≤ centralizer ({u} : Set G) := by
        rw [← hgen]
        refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp hh)))
        intro q hq
        exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hq (d.module_le_core hu))
      intro q hq
      exact mem_centralizer_singleton_iff.mp (hRQ hq)
    have hrc : r ∈ centralizer (R : Set G) := by
      intro a ha
      have ham : a ∈ R.map (MulAut.conj x⁻¹).toMonoidHom := hRmap.symm ▸ ha
      obtain ⟨b,hb,hba⟩ := ham
      rw [← hba]
      change (MulAut.conj x⁻¹) b * (MulAut.conj x⁻¹) u =
        (MulAut.conj x⁻¹) u * (MulAut.conj x⁻¹) b
      simpa only [map_mul] using congrArg (MulAut.conj x⁻¹) (huc b hb)
    apply hrQ
    change r ∈ (K ⊔ S).pCoreIn 2
    rw [d.core_eq_centralizer]
    exact ⟨hrR,centralizer_le (d.module_le_core.trans d.core_le) hrc⟩
  let z := ⁅r,u⁆
  have hzZ : z ∈ Z := by
    change z ∈ ⁅U,R⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hrR hu
  have hline : zpowers z = Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzZ)
    rw [Nat.card_zpowers]
    have hz2 : z ^ 2 = 1 := by
      have hzU : z ∈ U := (le_normalizer_iff_commutator_le_right.mp
        ((d.R_le_S.trans le_sup_right).trans d.normalizes_module))
        (commutator_mem_commutator hrR hu)
      exact elemPow_eq_one_of_isElementaryAbelian (A := U) z hzU
    rw [orderOf_eq_prime hz2 hz1]
    exact d.commutator_card.le
  have hzQ : z ∈ Q := by
    have hn := (d.R_le_S.trans le_sup_right).trans d.normalizes_module
    exact d.module_le_core ((le_normalizer_iff_commutator_le_right.mp hn)
      (commutator_mem_commutator hrR hu))
  have hzR : z ∈ centralizer (R : Set G) :=
    centralizer_le R.le_normalizer (d.commutator_centralizes_normalizer hzZ)
  obtain ⟨E,D,hEQ,hEe,hEC,hprod,hd,hD,he,hcen⟩ := elementary_dihedral_split R Q r u z
    (d.module_le_core hu) hzQ hz1 hr2 hrQ hgen.symm
    (d.normalizes_core ((d.R_le_S.trans le_sup_right) hrR)) hzR rfl
    (by
      intro q hq
      rw [hline]
      change ⁅r,q⁆ ∈ ⁅(blockU K).map K.subtype,R⁆
      rw [← d.derived_eq_module_commutator]
      exact commutator_mem_commutator hrR (d.core_le hq))
  exact ⟨x,hx,u,hu,E,D,hEQ,hEe,hEC,hprod,hd,hD,he,hcen.trans hline,
    central_factor_relIndex_center R E D _ hprod hEC hd (hcen.trans hline) d.commutator_card⟩
/-- The initial group has an actual elementary-by-dihedral model. The first
factor is the ambient central factor constructed in the marked split. -/
theorem Input.exists_initial_dihedral_model (d : Input K R S Λ) :
    ∃ E : Subgroup G, E ≤ R ⊓ centralizer (R : Set G) ∧ IsElementaryAbelian 2 E ∧
      Nonempty (R ≃* E × DihedralGroup 4) := by
  obtain ⟨x,hx,u,hu,E,D,hEQ,hEe,hEC,hprod,hd,_,⟨eD⟩,_,_⟩ := d.exists_marked_dihedral_split
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting E D hd
    (hEC.trans (centralizer_le (show D ≤ R from hprod ▸ (le_sup_right : D ≤ E ⊔ D))))
  let f : R ≃* E × D := ((MulEquiv.subgroupCongr hprod).trans e.symm)
  exact ⟨E,le_inf (hEQ.trans d.core_le) hEC,hEe,
    ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl E) eD)⟩⟩

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
