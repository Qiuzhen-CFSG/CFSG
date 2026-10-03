module
public import Theory.Character.InvolutionRootInduction
public import Theory.Character.InvolutionRootVanishing

/-!
# Recovering a function from involution roots

When the involutions form one conjugacy class, a class function vanishing on
odd-order elements is induced from its restriction to roots of a fixed
involution. Set the restriction to zero away from those roots. Uniqueness of
the involution in a cyclic group gives the induction formula at roots; fusion
covers every even-order element. This also preserves the involution-pair
pairing by the root-pair theorem.

Source: the involution-root induction argument of Wong (1964), Lemma 4,
article p.98, applied to arbitrary class functions.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

namespace Theory.Character

@[expose] public def involutionRootRestriction {G : Type*} [Group G] (t : G)
    (f : ClassFunction G) : ClassFunction (Subgroup.centralizer ({t} : Set G)) :=
  fun a => if t ∈ Subgroup.zpowers (a : G) then f a else 0

public theorem involutionRootRestriction_supported {G : Type*} [Group G] (t : G)
    (f : ClassFunction G) (a : Subgroup.centralizer ({t} : Set G))
    (ha : t ∉ Subgroup.zpowers (a : G)) : involutionRootRestriction t f a = 0 := by
  simp [involutionRootRestriction, ha]

private theorem induced_isClassFunction {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (f : ClassFunction H) : IsClassFunction (inducedClassFunction H f) := by
  intro a g
  unfold inducedClassFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro z
  have heq : (g⁻¹ * z)⁻¹ * a * (g⁻¹ * z) = z⁻¹ * (g * a * g⁻¹) * z := by group
  change (if h : z⁻¹ * (g * a * g⁻¹) * z ∈ H then f ⟨_, h⟩ else 0) =
    (if h : (g⁻¹ * z)⁻¹ * a * (g⁻¹ * z) ∈ H then f ⟨_, h⟩ else 0)
  simp only [heq]

public theorem involutionRootRestriction_isClassFunction {G : Type*} [Group G]
    (t : G) {f : ClassFunction G} (hf : IsClassFunction f) :
    IsClassFunction (involutionRootRestriction t f) := by
  intro a g
  let e := MulAut.conj (g : G)
  have het : e t = t := by
    change (g : G) * t * (g : G)⁻¹ = t
    rw [Subgroup.mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have hiff : t ∈ Subgroup.zpowers (e (a : G)) ↔ t ∈ Subgroup.zpowers (a : G) := by
    change t ∈ Subgroup.zpowers (e.toMonoidHom (a : G)) ↔ _
    rw [← e.toMonoidHom.map_zpowers]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, het] using
      (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
        (K := Subgroup.zpowers (a : G)) (x := t))
  change (if t ∈ Subgroup.zpowers (e (a : G)) then f (e a) else 0) = _
  exact if_congr hiff (hf a g) rfl

/-- A class function vanishing at odd-order elements is recovered by induction
from its restriction to the roots of an involution, when all involutions fuse. -/
public theorem induced_involutionRootRestriction {G : Type*} [Group G] [Fintype G]
    (t : G) (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (f : ClassFunction G) (hf : IsClassFunction f)
    (hodd : ∀ a : G, Odd (orderOf a) → f a = 0) :
    inducedClassFunction (Subgroup.centralizer ({t} : Set G))
      (involutionRootRestriction t f) = f := by
  ext a
  by_cases ha : 2 ∣ orderOf a
  · obtain ⟨b, hb, hab⟩ := exists_isConj_involution_root_of_even t hfuse a ha
    obtain ⟨g, hg⟩ := isConj_iff.mp hab
    have hi := induced_isClassFunction (Subgroup.centralizer ({t} : Set G))
      (involutionRootRestriction t f) a g
    rw [hg] at hi
    rw [← hi, inducedClassFunction_involutionRoots_apply t ht _
      (involutionRootRestriction_isClassFunction t hf)
      (involutionRootRestriction_supported t f) b hb]
    simp only [involutionRootRestriction, if_pos hb]
    rw [← hg, hf a g]
  · have ho : Odd (orderOf a) := (Nat.not_even_iff_odd).mp (by simpa [even_iff_two_dvd] using ha)
    rw [hodd a ho]
    apply inducedClassFunction_involutionRoots_eq_zero t _
      (involutionRootRestriction_supported t f)
    intro g hm
    have hd := orderOf_dvd_of_mem_zpowers hm
    rw [ht] at hd
    have he : orderOf (g⁻¹ * a * g) = orderOf a := by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
    exact ha (he ▸ hd)

end Theory.Character
