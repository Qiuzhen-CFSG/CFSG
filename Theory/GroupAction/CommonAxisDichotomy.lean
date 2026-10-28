module
public import Theory.GroupAction.CommonAxisCentralDisplacement
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# The unique nontrivial action with common binary axis

An automorphism fixing an index-two subgroup pointwise is determined by
one value outside it. Hence a nontrivial such automorphism has exactly that
fixed subgroup. If a conjugation action has displacements in a group of
order two, it is either trivial or has image of order two with exactly
the specified fixed hyperplane and commutator subgroup.
Source application: Aschbacher--Smith 14.3.19(2), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup
namespace MulAut
variable {V : Type*} [Group V]
theorem fixed_iff_mem_of_index_two (α : MulAut V) (C : Subgroup V)
    (hi : C.index=2) (hf : ∀ x∈C,α x=x) (hne : α≠1) (x:V) :
    α x=x ↔ x∈C := by
  refine ⟨fun hx=>?_,hf x⟩
  by_contra hxc
  apply hne
  apply MulEquiv.ext
  intro y
  change α y=y
  by_cases hy : y∈C
  · exact hf y hy
  · have hxy : x⁻¹*y∈C := by
      rw [C.mul_mem_iff_of_index_two hi,inv_mem_iff]
      exact iff_of_false hxc hy
    calc
      α y=α (x*(x⁻¹*y)) := by rw [mul_inv_cancel_left]
      _=α x*α (x⁻¹*y) := map_mul _ _ _
      _=y := by rw [hx,hf _ hxy,mul_inv_cancel_left]
end MulAut

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem conjugation_dichotomy_of_fixed_hyperplane
    (A D C Z : Subgroup G) (hDA : D≤normalizer (A:Set G))
    (hCA : C≤A) (hZA : Z≤A) (hAc : Nat.card A=16)
    (hCc : Nat.card C=8) (hZc : Nat.card Z=2)
    (hfix : D≤centralizer (C:Set G)) (hcomm : ⁅A,D⁆≤Z) :
    D≤centralizer (A:Set G) ∨
    (Nat.card (A.normalizerMonoidHom.comp (inclusion hDA)).range=2 ∧
      ⁅A,D⁆=Z ∧ ∀d:G,d∈D→d∉centralizer (A:Set G)→
        ∀a:G,a∈A→(Commute d a ↔ a∈C)) := by
  by_cases hd : D≤centralizer (A:Set G)
  · exact Or.inl hd
  right
  let ρ := A.normalizerMonoidHom.comp (inclusion hDA)
  have hρne : ρ.range≠⊥ := by
    intro he
    apply hd
    intro d hd
    apply mem_centralizer_iff.mpr
    intro a ha
    have hα : ρ ⟨d,hd⟩=1 := mem_bot.mp (he ▸ (show ρ ⟨d,hd⟩∈ρ.range from ⟨⟨d,hd⟩,rfl⟩))
    have hh := congrArg (fun α:MulAut A=>(α ⟨a,ha⟩:G)) hα
    change d*a*d⁻¹=a at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hρc : Nat.card ρ.range=2 := by
    have hl := (one_lt_card_iff_ne_bot ρ.range).mpr hρne
    have hu := conjugation_card_le_two_of_fixed_hyperplane A D C Z hDA hCA hZA
      hAc hCc hZc hfix hcomm
    change Nat.card ρ.range≤2 at hu
    omega
  have hcommne : ⁅A,D⁆≠⊥ := by
    intro he
    exact hd (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hcommZ : ⁅A,D⁆=Z := eq_of_le_of_card_ge hcomm (by
    have hl := (one_lt_card_iff_ne_bot ⁅A,D⁆).mpr hcommne
    rw [hZc]
    omega)
  refine ⟨hρc,hcommZ,?_⟩
  intro d hd hn a ha
  let α : MulAut A := ρ ⟨d,hd⟩
  have hαne : α≠1 := by
    intro he
    apply hn
    apply mem_centralizer_iff.mpr
    intro b hb
    have hh := congrArg (fun β:MulAut A=>(β ⟨b,hb⟩:G)) he
    change d*b*d⁻¹=b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hc : Nat.card (C.subgroupOf A)=8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv).trans hCc
  have hi : (C.subgroupOf A).index=2 := by
    have hh := (C.subgroupOf A).card_mul_index
    rw [hc,hAc] at hh
    omega
  have hf (x:A) (hx:x∈C.subgroupOf A) : α x=x := by
    apply Subtype.ext
    change d*(x:G)*d⁻¹=(x:G)
    rw [←mem_centralizer_iff.mp (hfix hd) (x:G) hx,mul_inv_cancel_right]
  have hh := MulAut.fixed_iff_mem_of_index_two α (C.subgroupOf A) hi hf hαne ⟨a,ha⟩
  rw [Subtype.ext_iff] at hh
  change (d*a*d⁻¹=a) ↔ a∈C at hh
  rw [mul_inv_eq_iff_eq_mul] at hh
  exact hh
end Subgroup
