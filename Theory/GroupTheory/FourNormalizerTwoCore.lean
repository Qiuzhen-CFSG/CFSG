module
public import Theory.GroupTheory.SymmetricFourNormalFour
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
# The two-core of a normal four-group action

A symmetric-four subgroup containing a normal elementary four induces its
full S₃ automorphism group. If the four's centralizer is a two-group, this
centralizer is exactly the ambient two-core: the kernel lies in O₂, while
S₃ has trivial two-core. This gives Q_E=C_S(E) in Aschbacher--Smith
2.5.15, printed p.559.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem twoCore_eq_centralizer_of_normal_four_symmetric_overgroup
    (E D : Subgroup G) [E.Normal] [IsKleinFour E] (hED : E ≤ D)
    (e : D ≃* Equiv.Perm (Fin 4)) (hc : IsPGroup 2 (centralizer (E : Set G))) :
    pCore 2 G = centralizer (E : Set G) := by
  let F := E.subgroupOf D
  let eF := subgroupOfEquivOfLe hED
  let : IsKleinFour F := {
    card_four := (Nat.card_congr eF.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).trans IsKleinFour.exponent_two }
  have hC := normal_four_selfCentralizing_of_equiv e F
  let f : G →* MulAut E := MulAut.conjNormal
  let g : D →* MulAut E := f.comp D.subtype
  have hfk : f.ker = centralizer (E : Set G) := by
    ext x
    constructor
    · intro hx e he
      have hh := congrArg (fun a : MulAut E => a ⟨e,he⟩) (MonoidHom.mem_ker.mp hx)
      have hv := congrArg Subtype.val hh
      change x * e * x⁻¹ = e at hv
      exact (mul_inv_eq_iff_eq_mul.mp hv).symm
    · intro hx
      apply MonoidHom.mem_ker.mpr
      ext y
      change x * (y : G) * x⁻¹ = (y : G)
      rw [← hx y y.property, mul_inv_cancel_right]
  have hgk : g.ker = F := by
    ext x
    change x ∈ f.ker.comap D.subtype ↔ _
    rw [hfk]
    change ((x : G) ∈ centralizer (E : Set G)) ↔ x ∈ F
    constructor
    · intro hx
      apply hC ▸ (show x ∈ centralizer (F : Set D) from ?_)
      intro y hy
      exact Subtype.ext (hx y hy)
    · intro hx
      let : IsMulCommutative E := IsKleinFour.isMulCommutative
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance hx
  have hgc : Nat.card g.range = 6 := by
    have hh := g.ker.card_mul_index
    rw [index_ker] at hh
    rw [hgk, IsKleinFour.card_four] at hh
    have hd : Nat.card D = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    omega
  have hgs : Function.Surjective g := MonoidHom.range_eq_top.mp
    (eq_top_of_card_eq g.range (hgc.trans (IsKleinFour.card_mulAut E).symm))
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨d,hd⟩ := hgs a
    exact ⟨d,hd⟩
  exact le_antisymm (hfk ▸ IsKleinFour.twoCore_le_ker_of_surjective E f hfs)
    (le_sSup ⟨inferInstance,hc⟩)
end Theory.GroupTheory
