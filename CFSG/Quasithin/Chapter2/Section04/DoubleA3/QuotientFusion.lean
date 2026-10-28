module

public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Counting
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed

/-!
# Fusion of the six outside quotient involutions

All odd involutions of the natural S₆ are conjugate in the actual Aut(A₆).
The two S₆ classes have cycle types 2 and 2³. The exceptional automorphism
of S₆ conjugates their induced A₆ automorphisms, so both classes fuse.
Transport through the original centralizer quotient supplies the conjugators
needed by `outside_quotient_fiber_count`; uniform fiber size is not a premise.

Source: Aschbacher–Smith §2.4, final paragraph, printed p.550.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup Equiv Equiv.Perm
open AlternatingSix.ShadowLocal GLS3.Chapter5

private theorem outer_intertwines (σ : Perm (Fin 6)) (a : A6) :
    outerAltAut (permutationAction σ a) =
      permutationAction (outerHom σ) (outerAltAut a) := by
  apply Subtype.ext
  change outerHom (σ * a.val * σ⁻¹) = outerHom σ * outerHom a.val * (outerHom σ)⁻¹
  simp only [map_mul, map_inv]

private theorem outer_conjugates (σ : Perm (Fin 6)) :
    IsConj (permutationAction σ) (permutationAction (outerHom σ)) := by
  apply isConj_iff.mpr
  refine ⟨outerAltAut, ?_⟩
  ext a : 1
  change outerAltAut (permutationAction σ (outerAltAut.symm a)) =
    permutationAction (outerHom σ) a
  rw [outer_intertwines, MulEquiv.apply_symm_apply]

/-- The two odd involution classes of S₆ fuse under its exceptional
outer automorphism, acting on the actual alternating group. -/
theorem natural_odd_involution_fusion (σ : Perm (Fin 6))
    (hσ : orderOf σ = 2) (hodd : σ ∉ alternatingGroup (Fin 6)) :
    IsConj (permutationAction (swap (4 : Fin 6) 5)) (permutationAction σ) := by
  rcases odd_involution_cycleType σ hσ hodd with hs | ht
  · exact permutationAction.map_isConj (isConj_of_cycleType_eq
      ((show (swap (4 : Fin 6) 5).cycleType = {2} by decide +kernel).trans
        (isSwap_iff_cycleType.mp hs).symm))
  · exact (outer_conjugates (swap (4 : Fin 6) 5)).trans
      (permutationAction.map_isConj (isConj_of_cycleType_eq
        (outerHom_standardSwap_cycleType.trans ht.symm)))

/-- Every natural noninner involution in the literal automorphism group
is conjugate to the marked transposition. -/
theorem natural_outer_involution_fusion (β : AutA6) (hβ : β ^ 2 = 1)
    (hn : β ∈ natural) (hi : β ∉ AlternatingSix.ShadowLocal.inner) :
    IsConj (permutationAction (swap (4 : Fin 6) 5)) β := by
  obtain ⟨σ, hσ⟩ := hn
  change permutationAction σ = β at hσ
  subst β
  have hsquare : σ ^ 2 = 1 := permutationAction_injective (by
    simpa only [map_pow, map_one] using hβ)
  have hodd : σ ∉ alternatingGroup (Fin 6) := by
    intro h
    exact hi ⟨⟨σ, h⟩, (permutationAction_coe ⟨σ, h⟩).symm⟩
  have hne : σ ≠ 1 := fun h => hodd (h ▸ (alternatingGroup (Fin 6)).one_mem)
  exact natural_odd_involution_fusion σ (orderOf_eq_prime hsquare hne) hodd

/-- Construct a quotient representative and all actual quotient conjugators
from a marked Aut(A₆) centralizer quotient. No uniform-fiber premise remains. -/
theorem exists_uniform_quotient_fusion {H : Type*} [Group H]
    (B R K : Subgroup H) [B.Normal] (e : (H ⧸ B) ≃* AutA6)
    (hinner : (K.map (QuotientGroup.mk' B)).map e.toMonoidHom = AlternatingSix.ShadowLocal.inner)
    (hnatural : (R.map (QuotientGroup.mk' B)).map e.toMonoidHom ≤ natural) :
    ∃ u : H, ∀ q : H ⧸ B, q ∈ R.map (QuotientGroup.mk' B) → q ^ 2 = 1 →
      q ∉ K.map (QuotientGroup.mk' B) → IsConj (QuotientGroup.mk' B u) q := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective B
    (e.symm (permutationAction (swap (4 : Fin 6) 5)))
  refine ⟨u, ?_⟩
  intro q hq hq2 hqK
  have heq : e q ∉ AlternatingSix.ShadowLocal.inner := by
    intro h
    rw [← hinner] at h
    obtain ⟨q', hq', heq'⟩ := h
    exact hqK (e.injective heq' ▸ hq')
  have hf := natural_outer_involution_fusion (e q)
    (by rw [← map_pow, hq2, map_one])
    (hnatural (mem_map_of_mem e.toMonoidHom hq)) heq
  have hh := e.symm.toMonoidHom.map_isConj hf
  simpa only [hu, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh

end CFSG.Quasithin.Chapter2.DoubleA3
