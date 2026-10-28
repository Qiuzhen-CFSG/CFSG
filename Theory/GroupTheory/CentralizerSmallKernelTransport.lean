module
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting centralizer quotients with a kernel of order two

A group equivalence restricts to the literal element centralizers. Pulling
an epimorphism back along this restriction preserves its kernel order.
An elementary actor of rank two contained in the centralizer cannot lie in
that kernel: otherwise its order would be at most two and its rank at most one.

These elementary transport facts are used for the binary outer-centralizer
case of Aschbacher--Smith E.1.14(1), printed p.214. The required actual
model epimorphism is an explicit input, not a consequence of transport.
-/

public section
open Subgroup
namespace Theory.GroupTheory.CentralizerSmallKernelTransport
variable {G H Q : Type*} [Group G] [Group H] [Group Q]

/-- Restrict an actual group equivalence to the centralizers of corresponding elements. -/
def centralizerEquiv (e : G ≃* H) (z : G) :
    centralizer ({z} : Set G) ≃* centralizer ({e z} : Set H) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

theorem map_centralizer (e : G ≃* H) (z : G) :
    (centralizer ({z} : Set G)).map e.toMonoidHom = centralizer ({e z} : Set H) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (centralizerEquiv e z ⟨x, hx⟩).property
  · intro y hy
    exact ⟨e.symm y, ((centralizerEquiv e z).symm ⟨y, hy⟩).property,
      e.apply_symm_apply y⟩

/-- The quotient map is transported on the whole centralizer, with its literal kernel. -/
theorem exists_quotient_of_equiv [Finite G] [Finite H]
    (e : G ≃* H) (z : G) (π : centralizer ({e z} : Set H) →* Q)
    (hπ : Function.Surjective π) (hker : Nat.card π.ker = 2) :
    ∃ ρ : centralizer ({z} : Set G) →* Q,
      Function.Surjective ρ ∧ Nat.card ρ.ker = 2 := by
  let c := centralizerEquiv e z
  refine ⟨π.comp c.toMonoidHom, hπ.comp c.surjective, ?_⟩
  rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_comp_mulEquiv π c]
  exact (Nat.card_congr (c.symm.subgroupMap π.ker).toEquiv).symm.trans hker

/-- An elementary group of rank two cannot disappear into a kernel of order two. -/
theorem rank_two_not_le_kernel [Finite G] (A C : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hrank : Group.rank A = 2) (hAC : A ≤ C)
    (π : C →* Q) (hker : Nat.card π.ker = 2) : ¬ A.subgroupOf C ≤ π.ker := by
  intro h
  let := hA
  have hc : Nat.card A ≤ 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, ← hker]
    exact Nat.card_le_card_of_injective (inclusion h) (inclusion_injective h)
  have hr := IsElementaryAbelian.rank_le_of_card_le A (p := 2) (n := 1)
    (by simpa using hc)
  omega

end Theory.GroupTheory.CentralizerSmallKernelTransport
