module

public import Theory.GroupTheory.SemidihedralSixteenInvolutions
public import Theory.GroupTheory.SemidihedralOrderFourFusion
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import FeitThompson.BGsection1.theorem_1_13

/-!
# The Sylow and transfer reductions for J.2.7

An SD16 involution centralizer in a finite group with one involution class
is itself Sylow. Its canonical order-four elements cannot fuse: their squares
are the distinguished involution, so a conjugator would lie in the centralizer,
where a conjugate of a rotation is again a rotation. The order-four
transfer theorem consequently supplies a normal subgroup of index two.

These are reductions toward recognition, not a recognition theorem.
Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition

/-- Exactly the intrinsic local hypotheses extracted from the cubic quotient. -/
structure Hypotheses (W : Type*) [Group W] [Finite W] where
  z : W
  z_order : orderOf z = 2
  involutions_conjugate : ∀ x : W, orderOf x = 2 → IsConj x z
  centralizer_equiv : Nonempty
    (centralizer ({z} : Set W) ≃* Semidihedral.StandardModel 4 (by decide))

namespace Hypotheses
variable {W : Type*} [Group W] [Finite W] (h : Hypotheses W)
include h

abbrev C := centralizer ({h.z} : Set W)

def model : h.C ≃* Semidihedral.StandardModel 4 (by decide) :=
  h.centralizer_equiv.some

def rotation : h.C := h.model.symm (Semidihedral.standardRotation 4 (by decide))
def reflection : h.C := h.model.symm (Semidihedral.standardReflection 4 (by decide))

theorem rotation_order : orderOf h.rotation = 8 := by
  rw [rotation, MulEquiv.orderOf_eq, Semidihedral.standardRotation_order]
  decide

theorem reflection_order : orderOf h.reflection = 2 := by
  rw [reflection, MulEquiv.orderOf_eq, Semidihedral.standardReflection_order]

theorem conjugation : h.reflection * h.rotation * h.reflection⁻¹ = h.rotation ^ 3 := by
  simpa only [rotation, reflection, map_mul, map_inv, map_pow,
    show 2 ^ (4 - 2) - 1 = 3 from rfl] using
    congrArg h.model.symm (Semidihedral.standard_conjugation 4 (by decide))

theorem generators : closure ({h.rotation, h.reflection} : Set h.C) = ⊤ := by
  have he := congrArg (fun K => K.map h.model.symm.toMonoidHom)
    (Semidihedral.standard_generators 4 (by decide))
  simpa only [rotation, reflection, MulEquiv.coe_toMonoidHom,
    MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    map_top_of_surjective h.model.symm.toMonoidHom h.model.symm.surjective] using he

theorem centralizer_card : Nat.card h.C = 16 :=
  (Nat.card_congr h.model.toEquiv).trans (Semidihedral.standardModel_card 4 (by decide))

theorem centralizer_isPGroup : IsPGroup 2 h.C :=
  IsPGroup.of_card (n := 4) h.centralizer_card

/-- The actual centralizer is an ambient Sylow subgroup. -/
theorem centralizer_isSylow : ∃ S : Sylow 2 W, (S : Subgroup W) = h.C := by
  classical
  obtain ⟨Q, hCQ⟩ := h.centralizer_isPGroup.exists_le_sylow
  have hzQ : h.z ∈ (Q : Subgroup W) := hCQ
    (mem_centralizer_singleton_iff.mpr (Commute.refl _))
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  let : Nontrivial Q := ⟨⟨⟨h.z, hzQ⟩, 1, by
    intro heq
    have he : h.z = 1 := congrArg Subtype.val heq
    have := h.z_order
    simp [he] at this⟩⟩
  obtain ⟨t, _, htCenter, htNe, htSq⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := Q) (p := 2) (⊤ : Subgroup Q) top_ne_bot
  have ht : orderOf (t : W) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime htSq htNe
  obtain ⟨g, hgt⟩ := isConj_iff.mp (h.involutions_conjugate t ht)
  let S : Sylow 2 W := g • Q
  have hSC : (S : Subgroup W) ≤ h.C := by
    intro x hx
    change x ∈ ((g • Q : Sylow 2 W) : Subgroup W) at hx
    rw [Sylow.coe_subgroup_smul] at hx
    rcases Set.mem_smul_set.mp hx with ⟨q, hqQ, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute q (t : W) :=
      congrArg Subtype.val ((mem_center_iff.mp htCenter) ⟨q, hqQ⟩)
    change Commute ((MulAut.conj g) q) h.z
    simpa only [MulAut.conj_apply, hgt] using hc.map (MulAut.conj g)
  exact ⟨S, (S.is_maximal' h.centralizer_isPGroup hSC).symm⟩

/-- The center marking is forced by the unique involution in the cyclic center. -/
theorem rotation_four : (h.rotation ^ 4 : h.C).val = h.z := by
  let zC : h.C := ⟨h.z, mem_centralizer_singleton_iff.mpr (Commute.refl _)⟩
  have hzC : zC ∈ center h.C := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have hc : center h.C = zpowers (h.rotation ^ 4) :=
    Semidihedral.center_eq (by decide : 4 ≤ 4) _ _ h.rotation_order
      h.reflection_order h.conjugation h.generators
  rw [hc] at hzC
  have hr4 : orderOf (h.rotation ^ 4) = 2 := by
    rw [orderOf_pow, h.rotation_order]
    decide
  have he := IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨h.rotation ^ 4, mem_zpowers _⟩ : zpowers (h.rotation ^ 4)))
    (y := (⟨zC, hzC⟩ : zpowers (h.rotation ^ 4)))
    (by simpa only [← Subgroup.orderOf_coe] using hr4)
    (by simpa only [← Subgroup.orderOf_coe] using h.z_order)
  exact congrArg (fun x : zpowers (h.rotation ^ 4) => ((x : h.C) : W)) he

theorem product_square : (h.rotation * h.reflection) ^ 2 = h.rotation ^ 4 := by
  have hb2 : h.reflection ^ 2 = 1 := h.reflection_order ▸ pow_orderOf_eq_one _
  have hm := Semidihedral.move_pow h.rotation h.reflection 3 h.conjugation 1
  simp only [pow_one, mul_one] at hm
  calc
    _ = h.rotation * (h.reflection * h.rotation) * h.reflection := by
      simp only [pow_two, mul_assoc]
    _ = h.rotation * (h.rotation ^ 3 * h.reflection) * h.reflection := by rw [hm]
    _ = h.rotation ^ 4 := by
      rw [mul_assoc, mul_assoc, ← pow_two, hb2, mul_one, ← pow_succ']

/-- The two order-four classes cannot fuse even in the ambient group. -/
theorem order_four_nonfusion :
    ¬ IsConj ((h.rotation ^ 2 : h.C) : W) ((h.rotation * h.reflection : h.C) : W) := by
  rintro hf
  obtain ⟨g, hg⟩ := isConj_iff.mp hf
  have hfix : g * h.z * g⁻¹ = h.z := by
    have hs := congrArg (fun x : W => x ^ 2) hg
    change (MulAut.conj g) ((h.rotation ^ 2 : h.C) : W) ^ 2 = _ at hs
    rw [← map_pow] at hs
    simpa only [← Subgroup.coe_pow, ← pow_mul, h.product_square, h.rotation_four, MulAut.conj_apply] using hs
  let gC : h.C := ⟨g, mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hfix)⟩
  have hi : IsConj (h.rotation ^ 2) (h.rotation * h.reflection) :=
    isConj_iff.mpr ⟨gC, Subtype.ext hg⟩
  obtain ⟨v, hv⟩ := isConj_iff.mp hi
  have hb2 : h.reflection ^ 2 = 1 := h.reflection_order ▸ pow_orderOf_eq_one _
  have hcomm : Commute h.rotation (h.rotation * h.reflection) := by
    rw [← hv]
    obtain ⟨i, _, rfl | rfl⟩ := Semidihedral.normal_form _ _ 8 3 (by decide)
      h.rotation_order hb2 h.conjugation h.generators v
    · rw [(Commute.pow_pow_self h.rotation i 2).mul_inv_cancel]
      exact Commute.self_pow _ _
    · have he : (h.rotation ^ i * h.reflection) * h.rotation ^ 2 *
          (h.rotation ^ i * h.reflection)⁻¹ =
          h.rotation ^ i * (h.reflection * h.rotation ^ 2 * h.reflection⁻¹) *
            (h.rotation ^ i)⁻¹ := by group
      rw [he, ← conj_pow, h.conjugation, ← pow_mul,
        (Commute.pow_pow_self h.rotation i 6).mul_inv_cancel]
      exact Commute.self_pow _ _
  apply Semidihedral.generators_not_commute (by decide : 4 ≤ 4)
    h.rotation_order h.conjugation
  change h.rotation * h.reflection = h.reflection * h.rotation
  apply mul_left_cancel (a := h.rotation)
  simpa only [mul_assoc] using hcomm.eq

/-- Order-four transfer gives a proper normal subgroup of index two. -/
theorem exists_normal_index_two : ∃ N : Subgroup W, N.Normal ∧ N.index = 2 := by
  classical
  by_contra! hn
  obtain ⟨S, hS⟩ := h.centralizer_isSylow
  let e : h.C ≃* S := MulEquiv.subgroupCongr hS.symm
  have hgen : closure ({e h.rotation, e h.reflection} : Set S) = ⊤ := by
    have he := congrArg (fun K => K.map e.toMonoidHom) h.generators
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      map_top_of_surjective e.toMonoidHom e.surjective, MulEquiv.coe_toMonoidHom] using he
  have hf := semidihedral_order_four_generators_isConj hn S 4 (by decide)
    ((Nat.card_congr e.symm.toEquiv).trans h.centralizer_card) (e h.rotation) (e h.reflection)
    (by rw [e.orderOf_eq]; exact h.rotation_order)
    (by rw [e.orderOf_eq]; exact h.reflection_order)
    (by simpa only [map_mul, map_inv, map_pow,
      show 2 ^ (4 - 2) - 1 = 3 from rfl] using congrArg e h.conjugation) hgen
  exact h.order_four_nonfusion (by
    simpa only [← map_pow, ← map_mul, show 2 ^ (4 - 3) = 2 from rfl,
      e, MulEquiv.subgroupCongr_apply] using hf)

/-- Involutions lie in every subgroup of index two: the distinguished one is
already a square, and normality transports this membership to its class. -/
theorem involution_mem_of_index_two (N : Subgroup W) (hi : N.index = 2)
    (x : W) (hx : orderOf x = 2) : x ∈ N := by
  let : N.Normal := N.normal_of_index_eq_two hi
  have hz : h.z ∈ N := by
    rw [← h.rotation_four]
    have hs := N.sq_mem_of_index_two hi (((h.rotation ^ 2 : h.C) : W))
    simpa only [← Subgroup.coe_pow, ← pow_mul] using hs
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.involutions_conjugate x hx).symm
  rw [← hg]
  exact (inferInstance : N.Normal).conj_mem _ hz _

/-- The centralizer meets both cosets of every subgroup of index two. -/
theorem centralizer_not_le_of_index_two (N : Subgroup W) (hi : N.index = 2) :
    ¬ h.C ≤ N := by
  intro hle
  obtain ⟨S, hS⟩ := h.centralizer_isSylow
  apply S.not_dvd_index
  rw [hS]
  exact hi ▸ index_dvd_of_le hle

/-- The ambient involution class remains a single class inside an index-two
subgroup. Adjust an outside conjugator by an outside element of C_W(z). -/
theorem involutions_conjugate_in_index_two (N : Subgroup W) (hi : N.index = 2)
    (x : N) (hx : orderOf x = 2) :
    IsConj x (⟨h.z, h.involution_mem_of_index_two N hi h.z h.z_order⟩ : N) := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (h.involutions_conjugate x ((Subgroup.orderOf_coe x).trans hx))
  by_cases hgN : g ∈ N
  · exact isConj_iff.mpr ⟨⟨g, hgN⟩, Subtype.ext hg⟩
  · have hc : ∃ c : W, c ∈ h.C ∧ c ∉ N := by
      by_contra! hc
      exact h.centralizer_not_le_of_index_two N hi hc
    obtain ⟨c, hcC, hcN⟩ := hc
    have hcg : c * g ∈ N := (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false hcN hgN)
    apply isConj_iff.mpr
    refine ⟨⟨c * g, hcg⟩, Subtype.ext ?_⟩
    change (c * g) * (x : W) * (c * g)⁻¹ = h.z
    calc
      _ = c * (g * (x : W) * g⁻¹) * c⁻¹ := by group
      _ = c * h.z * c⁻¹ := by rw [hg]
      _ = h.z := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hcC)

/-- Transfer makes the actual two-residual proper. -/
theorem twoResidual_ne_top : pResidual 2 W ≠ ⊤ := by
  obtain ⟨N, hn, hi⟩ := h.exists_normal_index_two
  let : N.Normal := hn
  have hp : IsPGroup 2 (W ⧸ N) := IsPGroup.of_card (n := 1) hi
  have hle : pResidual 2 W ≤ N := sInf_le ⟨hn, hp⟩
  intro he
  rw [he] at hle
  have ht : N = ⊤ := top_unique hle
  simp [ht] at hi

end Hypotheses
end CFSG.Quasithin.ChapterJ.SemidihedralRecognition
