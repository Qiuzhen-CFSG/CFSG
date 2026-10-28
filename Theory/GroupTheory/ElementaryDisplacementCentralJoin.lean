module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Displacement across a central summand

If an elementary group is the join of a fixed subgroup and a second subgroup,
a normalizing actor has the same possible commutator values on the join as on
the second subgroup. This transfers the E.2.3 fixed-plane calculation to the
actual Baumann-center group in Aschbacher–Smith 10.2.1, printed p.743.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement Pointwise
variable {G : Type*} [Group G]
theorem Subgroup.displacement_on_elementary_central_join (E C F K : Subgroup G) [IsElementaryAbelian 2 E]
    (he : E=C⊔F) (hC : C ≤ centralizer (K : Set G)) (g v : G)
    (hg : g ∈ K) (hgN : g ∈ normalizer (E : Set G)) (hf : ∀ x ∈ F, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v)
    (x : G) (hx : x ∈ E) : ⁅g,x⁆=1 ∨ ⁅g,x⁆=v := by
  have hCE : C ≤ E := he ▸ le_sup_left
  have hFE : F ≤ E := he ▸ le_sup_right
  have hCF : C ≤ normalizer (F : Set G) := by
    apply (show C ≤ centralizer (F : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro c hc f hf
    exact congrArg (fun z : E => (z : G)) (mul_comm (⟨f,hFE hf⟩ : E) ⟨c,hCE hc⟩)
  rw [he] at hx
  have hx' : x ∈ (C : Set G) * (F : Set G) := (coe_mul_of_left_le_normalizer_right C F hCF) ▸ hx
  obtain ⟨c,hc,f,hf',rfl⟩ := hx'
  have hgc : g*c=c*g := hC hc g hg
  have hcomm : ⁅g,c*f⁆=⁅g,f⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr hgc,one_mul]
    have hgf : ⁅g,f⁆ ∈ E := by
      exact E.mul_mem ((mem_normalizer_iff.mp hgN f).mp (hFE hf'))
        (E.inv_mem (hFE hf'))
    have hcc := congrArg (fun z : E => (z : G)) (mul_comm (⟨c,hCE hc⟩ : E) ⟨⁅g,f⁆,hgf⟩)
    change c * ⁅g,f⁆=⁅g,f⁆ * c at hcc
    rw [hcc,mul_inv_cancel_right]
  rw [hcomm]
  exact hf f hf'
