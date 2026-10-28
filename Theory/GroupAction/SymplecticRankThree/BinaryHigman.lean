module
public import Theory.GroupAction.SymplecticRankThree.BinaryAction
public import Theory.GroupAction.SymplecticRankThree.Kernel
public import Theory.GroupAction.SymplecticRankThree.RankThree
public import Theory.SpecificGroups.PSp4Three.Generation

/-!
# Higman's condition (i) over the binary field

The fifteen-point polarity design reconstructs its four-dimensional binary
alternating space. A nonidentity element of a pointwise polar-block kernel
fixes that block and interchanges the other two points on every line through
the pole. The reconstructed action is therefore the symplectic transvection
with that pole. Transitivity supplies every pole, and all symplectic
transvections generate the full matrix group.

Consequently the binary specialization of condition (i) gives an equivariant
isomorphism with full Sp₄(F₂), together with the reconstructed coordinates
and literal orthogonality relation. No model homomorphism, group order,
simplicity, or coordinatization is assumed. The final theorem starts from
the actual rank-three orbit data and kernel lower bound.

Source: Higman, Finite permutation groups of rank 3 (1964), §7 and
Theorem 2(i), pp.151–155. The printed theorem assumes q>2; this module
proves the q=2 extension directly, retaining all symplectic transvections.
-/

public noncomputable section
open Subgroup MulAction
open Theory.LinearAlgebra
open Matrix.PSp4Three
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω G : Type*} [Finite Ω] [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
variable (D : PolarityDesign Ω 2)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = 3)
variable (hdegree : Nat.card Ω = 15)
variable (hact : ∀ (g : G) a b, D.incident (g • a) (g • b) ↔ D.incident a b)
include hline hdegree

private theorem binary_third_point_add {a b c : Ω} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hl : D.line a b = {a,b,c}) :
    BinaryPolarGeometry.point D.incident a + BinaryPolarGeometry.point D.incident b =
      BinaryPolarGeometry.point D.incident c := by
  classical
  let d := D.binaryPolarData hline hdegree
  apply Subtype.ext
  funext w
  change BinaryPolarGeometry.row D.incident a w + BinaryPolarGeometry.row D.incident b w =
    BinaryPolarGeometry.row D.incident c w
  rw [d.row_symmetric a w,d.row_symmetric b w,d.row_symmetric c w]
  rcases D.binary_one_or_all hline hab hca hcb hl w with h | h | h | h <;>
    simp [BinaryPolarGeometry.row,h.1,h.2.1,h.2.2,show (1 : ZMod 2)+1=0 from rfl]

include hact in
/-- The nontrivial polar-block kernel element is the actual binary transvection. -/
theorem binary_kernel_transvection
    (E : BinaryPolarGeometry.Space D.incident ≃ₗ[ZMod 2] Vector 2 (ZMod 2))
    (j : G →* Sp 2 (ZMod 2))
    (heq : ∀ g x, E (BinaryPolarGeometry.point D.incident (g • x)) =
      j g • E (BinaryPolarGeometry.point D.incident x))
    (horth : ∀ x y, form (E (BinaryPolarGeometry.point D.incident x))
      (E (BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y)
    (a : Ω) (k : fixingSubgroup G (D.block a)) (hk : k ≠ 1) :
    j k = transvection (E (BinaryPolarGeometry.point D.incident a)) 1 := by
  let d := D.binaryPolarData hline hdegree
  have hf := (mem_fixingSubgroup_iff G).mp k.property
  have hp (x : Ω) :
      j k • E (BinaryPolarGeometry.point D.incident x) =
        transvection (E (BinaryPolarGeometry.point D.incident a)) 1 •
          E (BinaryPolarGeometry.point D.incident x) := by
    rw [← heq,transvection_apply,one_mul]
    by_cases hax : D.incident a x
    · rw [hf x hax,(horth x a).mpr (D.symm hax),zero_smul,add_zero]
    · have hne : a ≠ x := fun h => hax (h ▸ D.refl a)
      obtain ⟨c,hca,hcx,hl⟩ := D.binary_third_point hline hne
      have hmem := D.map_mem_line_of_fixes_block (MulAction.toPerm (k : G)) (hact k) hf x
      change (k : G) • x ∈ D.line a x at hmem
      rw [hl] at hmem
      have hmove : (k : G) • x ≠ x := fun he => hk (D.kernel_fixed_eq_one hact (by decide) hax k he)
      have hnota : (k : G) • x ≠ a := by
        intro hka
        have he := MulAction.injective (k : G) (hka.trans (hf a (D.refl a)).symm)
        exact hne he.symm
      have hkc : (k : G) • x = c := hmem.resolve_left hnota |>.resolve_left hmove
      have hform : form (E (BinaryPolarGeometry.point D.incident x))
          (E (BinaryPolarGeometry.point D.incident a)) = 1 := by
        have hn : form (E (BinaryPolarGeometry.point D.incident x))
            (E (BinaryPolarGeometry.point D.incident a)) ≠ 0 := fun hz => hax (D.symm ((horth x a).mp hz))
        have hcases (t : ZMod 2) : t=0 ∨ t=1 := by
          fin_cases t
          · exact Or.inl rfl
          · exact Or.inr rfl
        exact (hcases _).resolve_left hn
      rw [hkc,hform,one_smul,← D.binary_third_point_add hline hdegree hne hca hcx hl,map_add,add_comm]
  apply ext_action
  intro v
  obtain hv | ⟨x,hx⟩ := BinaryPointMap.eq_zero_or_mem_range _ d.point_add
    (BinaryPolarGeometry.Data.span_points (R := D.incident)) (E.symm v)
  · have hv0 : v = 0 := by simpa using congrArg E hv
    rw [hv0]
    simp only [smul_zero]
  · have hvx : E (BinaryPolarGeometry.point D.incident x) = v := by
      rw [hx,E.apply_symm_apply]
    rw [← hvx]
    exact hp x

include hact in
/-- Binary incidence and the nontrivial block kernel give the full symplectic action. -/
theorem binary_symplectic_equiv_of_kernel [IsPretransitive G Ω] (a : Ω)
    (hk : 2 ≤ Nat.card (fixingSubgroup G (D.block a))) :
    ∃ E : BinaryPolarGeometry.Space D.incident ≃ₗ[ZMod 2] Vector 2 (ZMod 2),
    ∃ e : G ≃* Sp 2 (ZMod 2),
      (∀ g x, E (BinaryPolarGeometry.point D.incident (g • x)) =
        e g • E (BinaryPolarGeometry.point D.incident x)) ∧
      (∀ x y, form (E (BinaryPolarGeometry.point D.incident x))
        (E (BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y) := by
  let d := D.binaryPolarData hline hdegree
  obtain ⟨E,j,hj,heq,horth⟩ := D.binary_action_embedding hline hdegree hact
  let : Finite G := Finite.of_injective j hj
  let : Nontrivial (fixingSubgroup G (D.block a)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k,hkne⟩ := exists_ne (1 : fixingSubgroup G (D.block a))
  have hbase : transvection (E (BinaryPolarGeometry.point D.incident a)) 1 ∈ j.range := by
    exact ⟨k,D.binary_kernel_transvection hline hdegree hact E j heq horth a k hkne⟩
  have hpoint (x : Ω) : transvection (E (BinaryPolarGeometry.point D.incident x)) 1 ∈ j.range := by
    obtain ⟨g,hg⟩ := exists_smul_eq G a x
    have hmem := j.range.mul_mem (j.range.mul_mem (show j g ∈ j.range from ⟨g,rfl⟩) hbase)
      (j.range.inv_mem (show j g ∈ j.range from ⟨g,rfl⟩))
    rw [transvection_conjugate,← heq,hg] at hmem
    exact hmem
  have hall (v : Vector 2 (ZMod 2)) (t : ZMod 2) : transvection v t ∈ j.range := by
    have ht : t=0 ∨ t=1 := by
      fin_cases t
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ht with rfl | rfl
    · rw [transvection_zero]
      exact j.range.one_mem
    · obtain hv | ⟨x,hx⟩ := BinaryPointMap.eq_zero_or_mem_range _ d.point_add
        (BinaryPolarGeometry.Data.span_points (R := D.incident)) (E.symm v)
      · have hv0 : v = 0 := by simpa using congrArg E hv
        rw [hv0,transvection_zero_vector]
        exact j.range.one_mem
      · have hvx : E (BinaryPolarGeometry.point D.incident x) = v := by
          rw [hx,E.apply_symm_apply]
        exact hvx ▸ hpoint x
  have hgen : transvectionGroup 2 (ZMod 2) ≤ j.range := by
    apply (closure_le _).mpr
    rintro g ⟨v,t,rfl⟩
    exact hall v t
  rw [transvectionGroup_eq_top] at hgen
  let e := MulEquiv.ofBijective j ⟨hj,MonoidHom.range_eq_top.mp (top_unique hgen)⟩
  exact ⟨E,e,heq,horth⟩

end Theory.GroupAction.SymplecticRankThree.PolarityDesign

namespace Theory.GroupAction.SymplecticRankThree
variable {G Ω : Type*} [Group G] [Fintype Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] [IsPreprimitive G Ω]

/-- The binary condition-(i) theorem, with coordinates, equivariance and full Sp₄(2). -/
theorem binary_condition_i_recognition
    (a b c : Ω) (hab : a ≠ b) (t : G) (hta : t • a = b) (htb : t • b = a)
    (hc : orbit (stabilizer G a) c = (insert a (orbit (stabilizer G a) b))ᶜ)
    (hdegree : Nat.card Ω = 15)
    (hsubdegree : Nat.card (orbit (stabilizer G a) b) = 6)
    (hk : 2 ≤ Nat.card (fixingSubgroup G (insert a (orbit (stabilizer G a) b)))) :
    ∃ D : PolarityDesign Ω 2,
      (∀ x y, D.incident x y ↔ y = x ∨ (SwappedOrbital.graph a b hab t hta htb).Adj x y) ∧
      D.block a = insert a (orbit (stabilizer G a) b) ∧
      ∃ E : BinaryPolarGeometry.Space D.incident ≃ₗ[ZMod 2] Vector 2 (ZMod 2),
      ∃ e : G ≃* Sp 2 (ZMod 2),
        (∀ g x, E (BinaryPolarGeometry.point D.incident (g • x)) =
          e g • E (BinaryPolarGeometry.point D.incident x)) ∧
        (∀ x y, form (E (BinaryPolarGeometry.point D.incident x))
          (E (BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y) := by
  obtain ⟨D,hD,hblock,hline⟩ := condition_i_lines (by decide : 2 ≤ 2)
    a b c hab t hta htb hc hdegree hsubdegree hk
  have hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y := by
    intro g x y
    rw [hD,hD,SwappedOrbital.adj_smul_iff]
    exact or_congr (MulAction.injective g).eq_iff Iff.rfl
  obtain ⟨E,e,heq,horth⟩ := D.binary_symplectic_equiv_of_kernel hline hdegree hact a
    (hblock.symm ▸ hk)
  exact ⟨D,hD,hblock,E,e,heq,horth⟩

end Theory.GroupAction.SymplecticRankThree
