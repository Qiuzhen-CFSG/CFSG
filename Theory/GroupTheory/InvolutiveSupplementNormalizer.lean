module
public import Theory.GroupTheory.TwoCosetExtension
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Involutions normalizing a faithful local supplement

Suppose D complements Q in P and a subgroup C normalizes both factors,
with C intersect P contained in D. If Q has no nonidentity C-fixed element,
an involution in P normalizing D and C already belongs to D.

Adjoining the involution gives at most two D-cosets. Its intersection with
Q therefore has at most one nonidentity element, fixed by all of C. The
fixed-point hypothesis kills that intersection, and supplementation finishes.
Only the displayed relative normalization is used; no ambient normality or
finiteness is needed.

The source consumer is the reflection-adjoined actor in DGS, Groups and
Graphs (1985), (14.3) and (14.9), pp.212,215.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An involution normalizing a faithful supplement and its controlling Cartan
already belongs to the supplement when the kernel has no Cartan fixed points. -/
theorem involution_mem_supplement_of_cartan_control
    (D Q C P : Subgroup G) (hDP : D ≤ P) (hgen : D ⊔ Q=P)
    (hDQ : Disjoint D Q) (hPQ : P ≤ normalizer (Q : Set G))
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
  have huniq (x y : G) (hx : x∈E ⊓ Q) (hy : y∈E ⊓ Q)
      (hxn : x≠1) (hyn : y≠1) : x=y := by
    have hxD : x∉D := fun hd => hxn (disjoint_def.mp hDQ hd hx.2)
    have hyD : y∉D := fun hd => hyn (disjoint_def.mp hDQ hd hy.2)
    obtain ⟨d,hd,hxd⟩ := hx.1.resolve_left hxD
    obtain ⟨e,he,hye⟩ := hy.1.resolve_left hyD
    have hzD : x⁻¹*y∈D := by
      rw [hxd,hye]
      simpa only [mul_inv_rev, mul_assoc,inv_mul_cancel_left] using D.mul_mem (D.inv_mem hd) he
    have hz : x⁻¹*y=1 := disjoint_def.mp hDQ hzD (Q.mul_mem (Q.inv_mem hx.2) hy.2)
    exact inv_mul_eq_one.mp hz
  have hEQ : E ⊓ Q=⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply hfixed.le
    refine ⟨hx.2,mem_centralizer_iff.mpr ?_⟩
    intro c hc
    by_cases hx1 : x=1
    · rw [hx1]; simp
    have hcx : c*x*c⁻¹∈E ⊓ Q :=
      ⟨hconjE c hc x hx.1,(mem_normalizer_iff.mp (hCQ hc) x).mp hx.2⟩
    have hn : c*x*c⁻¹≠1 := by
      intro he
      apply hx1
      have hh := congrArg (fun z : G => c⁻¹*z*c) he
      simpa only [←mul_assoc,inv_mul_cancel,one_mul,inv_mul_cancel_right,
        mul_one] using hh
    have hh := huniq (c*x*c⁻¹) x hcx hx hn hx1
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hprod : (P : Set G)=(Q : Set G)*(D : Set G) := by
    rw [←hgen,sup_comm]
    exact coe_mul_of_right_le_normalizer_left Q D (hDP.trans hPQ)
  obtain ⟨q,hq,d,hd,hqd⟩ := hprod ▸ (show u∈(P : Set G) from huP)
  have hqE : q∈E := by
    have he : q=u*d⁻¹ := by rw [←hqd,mul_inv_cancel_right]
    rw [he]
    exact E.mul_mem huE (E.inv_mem (hDE hd))
  have hq1 : q=1 := hEQ.le ⟨hqE,hq⟩
  have he : d=u := by simpa only [hq1,one_mul] using hqd
  exact he ▸ hd

end Theory.GroupTheory
