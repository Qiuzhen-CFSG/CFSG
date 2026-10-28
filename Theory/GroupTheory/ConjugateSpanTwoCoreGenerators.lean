module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Two conjugate spaces generate the original orbit span

Let U be the K-span of E, with H normalizing U. Suppose V and one
K-conjugate generate K's image modulo O₂(H). If [U,V] lies in E and
[U,O₂(H)] lies in a subgroup Z of E, then E joined with its selected
conjugate is invariant under both generators and the full kernel. It is
therefore K-invariant and equals U. No fixed-space vanishing is needed.

Source application: Aschbacher--Smith 8.3.12, printed p.726,
refs/quasithin.pdf. The original point line is retained in Z.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Displacement bounds and two quotient generators make the full orbit span a two-space join. -/
theorem conjugateSpan_eq_two_conjugates_mod_twoCore
    (H K U V E Z : Subgroup G) (hKH : K ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hZE : Z ≤ E) (hEU : E ≤ U)
    (hUV : ⁅U,V⁆ ≤ E) (hUQ : ⁅U,H.pCoreIn 2⁆ ≤ Z)
    (hspan : U = conjugateSpanBy E K) (k : K)
    (hgen : let π := QuotientGroup.mk' (pCore 2 H)
      let A := (V.subgroupOf H).map π
      (K.subgroupOf H).map π ≤
        A ⊔ A.map (MulAut.conj (π (inclusion hKH k))).toMonoidHom) :
    U = E ⊔ E.conjBy (k : G) := by
  let W := E ⊔ E.conjBy (k : G)
  let π := QuotientGroup.mk' (pCore 2 H)
  let kH := inclusion hKH k
  have hkU : U.map (MulAut.conj (k : G)).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hHU (hKH k.property))
  have hW : W ≤ U := sup_le hEU ((map_mono hEU).trans hkU.le)
  have hVN : V ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hW le_rfl).trans hUV).trans le_sup_left)
  have hconj : ⁅U,V.conjBy (k : G)⁆ ≤ E.conjBy (k : G) := by
    have hh := map_mono (f := (MulAut.conj (k : G)).toMonoidHom) hUV
    rw [map_commutator,hkU] at hh
    exact hh
  have hVgN : V.conjBy (k : G) ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hW le_rfl).trans hconj).trans le_sup_right)
  have hQN : H.pCoreIn 2 ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((((commutator_mono hW le_rfl).trans hUQ).trans hZE).trans le_sup_left)
  let N := (normalizer (W : Set G)).subgroupOf H
  have hA : (V.subgroupOf H).map π ≤ N.map π := map_mono (subgroupOf_mono H hVN)
  have hAg : ((V.subgroupOf H).map π).map (MulAut.conj (π kH)).toMonoidHom ≤ N.map π := by
    rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨kH*v*kH⁻¹,?_,?_⟩
    · exact hVgN (mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom hv)
    · change π (kH*v*kH⁻¹) = π kH * π v * (π kH)⁻¹
      rw [map_mul,map_mul,map_inv]
  have hKN : K ≤ normalizer (W : Set G) := by
    intro x hx
    let xH : H := ⟨x,hKH hx⟩
    have hm : π xH ∈ N.map π := (hgen.trans (sup_le hA hAg))
      (mem_map_of_mem π hx)
    obtain ⟨y,hy,hyx⟩ := hm
    have hq : xH / y ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (xH / y) = 1
      rw [map_div,hyx,div_self']
    have hdiv : x / (y : G) ∈ normalizer (W : Set G) :=
      hQN (mem_map_of_mem H.subtype hq)
    have hh := (normalizer (W : Set G)).mul_mem hdiv hy
    change x / (y : G) * (y : G) ∈ normalizer (W : Set G) at hh
    simpa only [div_mul_cancel] using hh
  exact le_antisymm (hspan ▸ conjugateSpanBy_le le_sup_left hKN) hW
end Subgroup
