module
public import Theory.GroupAction.FixedQuotientCentralizer
public import Theory.GroupTheory.CentralProductProjection

/-!
# Extending a fixed quotient across a fixed supplement

Suppose an invariant abelian subgroup U is the product of an invariant W
and C_U(K). A marked quotient W/C_W(K) then extends to U/C_U(K), using
exactly the same actor and coefficient map on W. Multiplication from
W times C_U(K) descends the coefficient map; its exact kernel identifies
the quotient, and conjugation on the fixed factor proves equivariance.
No direct-product decomposition or vanishing fixed kernel is assumed.

The application is the natural moved-layer alternative in
Aschbacher--Smith 5.1.3(3) and 5.1.6(2), printed pp.630--632, where
Sylow-fixed generation supplies the supplement by B.2.14, printed p.78.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Representation.ConjugationQuotientModel
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {K U W : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- Extend the same quotient marking across an actor-fixed supplement. -/
theorem exists_extension_of_fixed_supplement
    [IsMulCommutative U] (m : ConjugationQuotientModel K W ρ)
    (hWU : W ≤ U) (hn : K ≤ normalizer (U : Set G))
    (hs : U = W ⊔ (U ⊓ centralizer (K : Set G))) :
    ∃ m' : ConjugationQuotientModel K U ρ,
      m'.actor = m.actor ∧ m'.quotient.comp (inclusion hWU) = m.quotient := by
  let C := U ⊓ centralizer (K : Set G)
  have hc : W ≤ centralizer (C : Set G) := by
    intro w hw c hc
    exact congrArg Subtype.val (mul_comm (⟨c,hc.1⟩ : U) ⟨w,hWU hw⟩)
  have hk : m.quotient.ker = C.subgroupOf W := by
    rw [m.kernel]
    ext w
    exact ⟨fun hw => ⟨hWU w.property,hw⟩,fun hw => hw.2⟩
  obtain ⟨π,hπ,hker⟩ := exists_sup_projection W C hc m.quotient hk
  let e : U ≃* (W ⊔ C : Subgroup G) := MulEquiv.subgroupCongr hs
  let q : U →* Multiplicative V := π.comp e.toMonoidHom
  have hq (w : W) : q (inclusion hWU w) = m.quotient w := hπ w
  have hqker : q.ker = (centralizer (K : Set G)).subgroupOf U := by
    ext u
    change e u ∈ π.ker ↔ _
    rw [hker]
    change ((u : G) ∈ U ∧ (u : G) ∈ centralizer (K : Set G)) ↔ _
    exact ⟨fun h => h.2,fun h => ⟨u.property,h⟩⟩
  have hqC (c : C) : q (inclusion inf_le_left c) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hqker]
    exact c.property.2
  refine ⟨{ normalizes := hn
            actor := m.actor
            quotient := q
            surjective := ?_
            kernel := hqker
            equivariant := ?_ },rfl,?_⟩
  · intro v
    obtain ⟨w,rfl⟩ := m.surjective v
    exact ⟨inclusion hWU w,hq w⟩
  · intro k u
    have hu : (u : G) ∈ W ⊔ C := hs ▸ u.property
    have hu' : (u : G) ∈ (W : Set G) * (C : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right W C
        (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hu
    obtain ⟨w,hw,c,hc',hprod⟩ := hu'
    let w' : W := ⟨w,hw⟩
    let c' : C := ⟨c,hc'⟩
    have hprod' : u = inclusion hWU w' * inclusion inf_le_left c' := Subtype.ext hprod.symm
    have hfix : U.normalizerMonoidHom ⟨k,hn k.property⟩
        (inclusion inf_le_left c') = inclusion inf_le_left c' := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc'.2 k k.property)
    have hconj : U.normalizerMonoidHom ⟨k,hn k.property⟩ (inclusion hWU w') =
        inclusion hWU (W.normalizerMonoidHom ⟨k,m.normalizes k.property⟩ w') := rfl
    rw [hprod',map_mul,hfix,hconj,map_mul,hq,hqC,mul_one,map_mul,hq,hqC,mul_one]
    exact m.equivariant k w'
  · ext w
    exact hq w
end Representation.ConjugationQuotientModel
