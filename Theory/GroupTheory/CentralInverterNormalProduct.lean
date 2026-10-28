module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A normal product from a centralizing and inverting element

Let Q and Y be normal. An element z centralizing Q and inverting Y acts
centrally in both automorphism groups. Thus every displacement [g,z]
centralizes QY. If C_G(QY) lies in QY, the image of z in G/QY is central,
and QY<z> is normal. This uses the literal quotient and needs no splitting.

Source application: the component-free branch of Aschbacher--Smith
2.5.3(4), printed p.553, with Q=O2(H) and Y=O(H).
-/

public section
namespace Theory.GroupTheory
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The involution/product normality argument only needs the stated
centralizing and inverting actions; the element need not have order two. -/
theorem normal_sup_zpowers_of_centralizes_inverts
    (Q Y : Subgroup G) [Q.Normal] [Y.Normal] (z : G)
    (hfix : z ∈ centralizer (Q : Set G))
    (hinv : ∀ y ∈ Y, z * y * z⁻¹ = y⁻¹)
    (hself : centralizer ((Q ⊔ Y : Subgroup G) : Set G) ≤ Q ⊔ Y) :
    (Q ⊔ Y ⊔ zpowers z).Normal := by
  let ρQ : G →* MulAut Q := MulAut.conjNormal
  let ρY : G →* MulAut Y := MulAut.conjNormal
  have hzQ : ρQ z = 1 := by
    ext q
    change z * (q : G) * z⁻¹ = (q : G)
    rw [← hfix q q.property]
    simp
  have hzY (y : Y) : ρY z y = y⁻¹ :=
    Subtype.ext (hinv y y.property)
  have hd (g : G) : ⁅g, z⁆ ∈ Q ⊔ Y := by
    apply hself
    suffices hc : ⁅g, z⁆ ∈ centralizer (Q : Set G) ∧
        ⁅g, z⁆ ∈ centralizer (Y : Set G) by
      rw [sup_eq_closure, centralizer_closure]
      intro x hx
      exact hx.elim (fun hq => hc.1 x hq) (fun hy => hc.2 x hy)
    constructor
    · rw [← MulAut.conjNormal_ker_eq_centralizer Q]
      change ρQ ⁅g, z⁆ = 1
      rw [map_commutatorElement, hzQ]
      simp
    · rw [← MulAut.conjNormal_ker_eq_centralizer Y]
      change ρY ⁅g, z⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      ext y
      simp only [MulAut.mul_apply, hzY, map_inv]
  let N := Q ⊔ Y
  let q := QuotientGroup.mk' N
  have hzcenter : q z ∈ center (G ⧸ N) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hd g)
  let Z := zpowers (q z)
  have hZcenter : Z ≤ center (G ⧸ N) := zpowers_le.mpr hzcenter
  let : Z.Normal := by
    constructor
    intro x hx a
    have he : a * x * a⁻¹ = x := by
      rw [mem_center_iff.mp (hZcenter hx) a]
      simp
    rwa [he]
  have he : Z.comap q = Q ⊔ Y ⊔ zpowers z := by
    change (zpowers (q z)).comap q = N ⊔ zpowers z
    rw [← MonoidHom.map_zpowers, comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  exact he ▸ (inferInstance : (Z.comap q).Normal)

end Theory.GroupTheory
