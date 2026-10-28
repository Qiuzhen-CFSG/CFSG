module
public import Theory.Representation.BinaryOffender.CentralCoverConjugateBudget
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget.Transport
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Elementary conjugate budgets on fixed-free actions

For a centerless actor, an inner automorphism budget pulls back to its
actual subgroups. Intersection of the fixed spaces of the generating
conjugates bounds the degree of any action with zero full fixed space.
Irreducibility is unnecessary. The concrete consumer is the original
C.5.13 moved dual with a putative PSL₂(11) actor.
Source: the conjugate-generation inequality used in Aschbacher–Smith K.2,
printed p.453, and C.5.13, printed p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
theorem elementaryBudget_of_inner {G : Type*} [_root_.Group G] (hc : center G = ⊥) {b : ℕ}
    (h : ElementaryInnerConjugateBudget G b) : ElementaryConjugateBudget G b := by
  let f : G →* MulAut G := MulAut.conj
  have hf : Function.Injective f := Theory.GroupTheory.conj_injective_of_center_eq_bot hc
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo (A.map f) := by
    refine ⟨?_,IsElementaryAbelian.map f⟩
    intro hz
    apply hA.1
    apply (map_injective hf)
    simpa only [Subgroup.map_bot] using hz
  obtain ⟨n,c,hn,hgen⟩ := h (A.map f) hB
  refine ⟨n,c,?_,?_⟩
  · simpa only [rank_map_injective f hf] using hn
  · apply top_unique
    apply (map_le_map_iff_of_injective hf).mp
    rw [← MonoidHom.range_eq_map, Subgroup.map_iSup]
    convert hgen using 1
    apply iSup_congr
    intro i
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f (c i*x*(c i)⁻¹) = f (c i)*f x*(f (c i))⁻¹
    rw [map_mul,map_mul,map_inv]
theorem finrank_le_of_fixed_cubic_budget {G V : Type*} [_root_.Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hfix : fixedSpace ρ ⊤ = ⊥) {a b : ℕ}
    (hbudget : ElementaryConjugateBudget G b) (hsmall : cubicRatio ρ ≤ a) :
    Module.finrank (ZMod 2) V ≤ a*b := by
  obtain ⟨A,hA,_,hcodim⟩ := (cubicRatio_le_nat_iff ρ a).mp hsmall
  obtain ⟨n,c,hn,hc⟩ := hbudget A hA
  have hdim := finrank_le_mul_fixedCodim_of_subgroup_conjugates ρ ⊤ A hfix c hc.ge
  calc
    _ ≤ n * fixedCodim ρ A := hdim
    _ ≤ n * (a * rank A) := Nat.mul_le_mul_left n hcodim
    _ = a * (n * rank A) := by ac_rfl
    _ ≤ a * b := Nat.mul_le_mul_left a hn
end Representation.BinaryOffender
