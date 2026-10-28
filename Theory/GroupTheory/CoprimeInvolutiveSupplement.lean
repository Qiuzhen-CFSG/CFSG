module
public import Theory.GroupTheory.InvolutiveSupplementNormalizer
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Nilpotent

/-!
# Coprime Cartan control of an involutive supplement

An involution normalizing a local supplement and its controlling odd Cartan
belongs to that supplement. The supplement may intersect the two-group
kernel nontrivially. Adjoining the involution adds at most two cosets; the
Cartan therefore fixes the quotient of the resulting kernel intersection.
Coprime fixed-point lifting and the original fixed-point-free kernel remove
the extra coset. No splitting of the supplement from the kernel is used.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem fixed_coset_mem_normal_subgroup
    (H N C : Subgroup G) [Finite H] [Finite C]
    (_hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G))
    (hCH : C ≤ normalizer (H : Set G)) (hCN : C ≤ normalizer (N : Set G))
    (hsolv : Group.IsSolvable H)
    (hcop : Nat.Coprime (Nat.card C) (Nat.card H))
    (hfree : H ⊓ centralizer (C : Set G) = ⊥)
    (x : G) (hx : x ∈ H)
    (hfix : ∀ c ∈ C, (c*x*c⁻¹)/x ∈ N) : x ∈ N := by
  let _ : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHN
  let _ : MulDistribMulAction C H := conjMulDistribMulActionOfLeNormalizer C H hCH
  have hInv : IsInvariant C H (N.subgroupOf H) :=
    ⟨fun c y => mem_normalizer_iff.mp (hCN c.property) y⟩
  let _ := quotientMulDistribMulAction (N.subgroupOf H) hInv
  let xH : H := ⟨x,hx⟩
  have hq : QuotientGroup.mk' (N.subgroupOf H) xH ∈
      FixedPoints.subgroup C (H ⧸ N.subgroupOf H) := by
    intro c
    change QuotientGroup.mk' _ (c • xH) = QuotientGroup.mk' _ xH
    exact QuotientGroup.eq_iff_div_mem.mpr (hfix c c.property)
  rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop _ hInv] at hq
  obtain ⟨y,hy,he⟩ := hq
  have hyC : (y : G) ∈ centralizer (C : Set G) := by
    apply mem_centralizer_iff.mpr
    intro c hc
    have hh := congrArg (fun z : H => (z : G)) (hy (⟨c,hc⟩ : C))
    change c*(y:G)*c⁻¹=(y:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hy1 : (y : G)=1 := hfree.le ⟨y.property,hyC⟩
  have hnH : y/xH ∈ N.subgroupOf H := QuotientGroup.eq_iff_div_mem.mp he
  have hn : (y : G)/x ∈ N := hnH
  simpa only [hy1,one_div,inv_mem_iff] using hn

/-- Coprime fixed-point lifting removes the binary extra coset even when the
local supplement has a nontrivial intersection with the two-group kernel. -/
theorem involution_mem_supplement_of_coprime_cartan_control
    (D Q C P : Subgroup G) [Finite Q] [Finite C]
    (hQ : IsPGroup 2 Q) (ho : Odd (Nat.card C))
    (hDP : D ≤ P) (hgen : D ⊔ Q=P)
    (hPQ : P ≤ normalizer (Q : Set G))
    (hCD : C ≤ normalizer (D : Set G)) (hCQ : C ≤ normalizer (Q : Set G))
    (hCP : C ⊓ P ≤ D) (hfixed : Q ⊓ centralizer (C : Set G)=⊥)
    (u : G) (huP : u∈P) (huD : u∈normalizer (D : Set G))
    (huC : u∈normalizer (C : Set G)) (hu2 : u*u=1) : u∈D := by
  let E := twoCosetExtension D u (hu2 ▸ D.one_mem)
    (fun d hd => by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp ((normalizer (D : Set G)).inv_mem huD) d).mp hd)
  have hDE : D ≤ E := fun _ hx => Or.inl hx
  have huE : u∈E := Or.inr ⟨1,D.one_mem,(mul_one u).symm⟩
  have hEP : E ≤ P := by
    rintro x (hx | ⟨d,hd,rfl⟩)
    · exact hDP hx
    · exact P.mul_mem huP (hDP hd)
  have hCnP : C ≤ normalizer (P : Set G) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←hgen,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hCD hc),
      mem_normalizer_iff_map_conj_eq.mp (hCQ hc)]
  have hconjE (c : G) (hc : c∈C) : ∀ x∈E, c*x*c⁻¹∈E := by
    have hcu : c*u*c⁻¹*u⁻¹∈D := by
      apply hCP
      constructor
      · have hh := (mem_normalizer_iff.mp huC c⁻¹).mp (C.inv_mem hc)
        have he : c*u*c⁻¹*u⁻¹=c*(u*c⁻¹*u⁻¹) := by group
        rw [he]
        exact C.mul_mem hc hh
      · exact P.mul_mem ((mem_normalizer_iff.mp (hCnP hc) u).mp huP) (P.inv_mem huP)
    intro x hx
    rcases hx with hx | ⟨d,hd,rfl⟩
    · exact hDE ((mem_normalizer_iff.mp (hCD hc) x).mp hx)
    · have he : c*(u*d)*c⁻¹=(c*u*c⁻¹*u⁻¹)*u*(c*d*c⁻¹) := by group
      rw [he]
      exact E.mul_mem (E.mul_mem (hDE hcu) huE)
        (hDE ((mem_normalizer_iff.mp (hCD hc) d).mp hd))
  have hEnD : E ≤ normalizer (D : Set G) := by
    rintro x (hx | ⟨d,hd,rfl⟩)
    · exact D.le_normalizer hx
    · exact (normalizer (D : Set G)).mul_mem huD (D.le_normalizer hd)
  have hCE : C ≤ normalizer (E : Set G) := by
    intro c hc
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hconjE c hc x
    · intro hx
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using
        hconjE c⁻¹ (C.inv_mem hc) (c*x*c⁻¹) hx
  let H := E ⊓ Q
  let N := D ⊓ Q
  have hNH : N ≤ H := inf_le_inf hDE le_rfl
  have hHN : H ≤ normalizer (N : Set G) := by
    intro x hx
    exact mem_normalizer_iff.mpr (fun y => and_congr
      (mem_normalizer_iff.mp (hEnD hx.1) y)
      (mem_normalizer_iff.mp (Q.le_normalizer hx.2) y))
  have hCH : C ≤ normalizer (H : Set G) := by
    intro c hc
    exact mem_normalizer_iff.mpr (fun y => and_congr
      (mem_normalizer_iff.mp (hCE hc) y) (mem_normalizer_iff.mp (hCQ hc) y))
  have hCN : C ≤ normalizer (N : Set G) := by
    intro c hc
    exact mem_normalizer_iff.mpr (fun y => and_congr
      (mem_normalizer_iff.mp (hCD hc) y) (mem_normalizer_iff.mp (hCQ hc) y))
  let _ : Finite H := Finite.of_injective (inclusion (show H ≤ Q from inf_le_right))
    (inclusion_injective _)
  have hpH : IsPGroup 2 H := hQ.to_le inf_le_right
  let _ : Group.IsNilpotent H := hpH.isNilpotent
  have hcop : Nat.Coprime (Nat.card C) (Nat.card H) := by
    obtain ⟨n,hn⟩ := hpH.exists_card_eq
    rw [hn]
    exact ho.coprime_two_right.pow_right n
  have hfree : H ⊓ centralizer (C : Set G)=⊥ :=
    bot_unique ((inf_le_inf_right _ (show H ≤ Q from inf_le_right)).trans hfixed.le)
  have hHD : H ≤ D := by
    intro x hx
    have hxN : x ∈ N := fixed_coset_mem_normal_subgroup H N C hNH hHN hCH hCN
      inferInstance hcop hfree x hx (by
        intro c hc
        let y := c*x*c⁻¹
        have hyE : y ∈ E := hconjE c hc x hx.1
        have hyQ : y ∈ Q := (mem_normalizer_iff.mp (hCQ hc) x).mp hx.2
        have hxyD : x⁻¹*y ∈ D := by
          by_cases hxD : x ∈ D
          · exact D.mul_mem (D.inv_mem hxD) ((mem_normalizer_iff.mp (hCD hc) x).mp hxD)
          · have hyD : y ∉ D := fun hh => hxD ((mem_normalizer_iff.mp (hCD hc) x).mpr hh)
            obtain ⟨d,hd,hxd⟩ := hx.1.resolve_left hxD
            obtain ⟨e,he,hye⟩ := hyE.resolve_left hyD
            rw [hxd,hye]
            simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using
              D.mul_mem (D.inv_mem hd) he
        have hyxD : y/x ∈ D := by
          have hh := (mem_normalizer_iff.mp (hEnD hx.1) (x⁻¹*y)).mp hxyD
          simpa only [mul_assoc,mul_inv_cancel_left,div_eq_mul_inv] using hh
        exact ⟨hyxD,Q.div_mem hyQ hx.2⟩)
    exact hxN.1
  have hprod : (P : Set G)=(Q : Set G)*(D : Set G) := by
    rw [←hgen,sup_comm]
    exact coe_mul_of_right_le_normalizer_left Q D (hDP.trans hPQ)
  obtain ⟨q,hq,d,hd,hqd⟩ := hprod ▸ (show u∈(P : Set G) from huP)
  have hqE : q∈E := by
    have he : q=u*d⁻¹ := by rw [←hqd,mul_inv_cancel_right]
    rw [he]
    exact E.mul_mem huE (E.inv_mem (hDE hd))
  exact hqd ▸ D.mul_mem (hHD ⟨hqE,hq⟩) hd

end Theory.GroupTheory
