module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Orbit
public import Theory.GroupTheory.CentralizerResidualProducts
/-!
# One representative suffices for the type U₄(3) core-intersection condition

The original centralizer hypothesis makes its residual transitive on the
noncentral involutions of the core. Conjugation by a residual element preserves
the marked core and transports the core of one fused involution to another.
Thus a calculation for one actual fusion element gives the source condition
for every fusion element, without assuming the additional IsType clauses.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.2(4), printed p.242.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CentralizerHypothesis
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem intersection_card_of_representative (h : CentralizerHypothesis z) (g₀ : G)
    (hg₀ : g₀⁻¹*z*g₀ ∈ core z) (hz₀ : g₀⁻¹*z*g₀ ∉ zpowers z)
    (hc : Nat.card (core z ⊓ conjugate (core z) g₀ : Subgroup G)=4)
    (g : G) (hg : g⁻¹*z*g ∈ core z) (hz : g⁻¹*z*g ∉ zpowers z) :
    Nat.card (core z ⊓ conjugate (core z) g : Subgroup G)=4 := by
  have horder (a : G) : orderOf (a⁻¹*z*a)=2 := by
    simpa only [MulAut.conj_apply,inv_inv] using ((MulAut.conj a⁻¹).orderOf_eq z).trans h.involution
  obtain ⟨k,hk,he⟩ := h.core_involution_orbit _ _ hg hg₀ (horder g) (horder g₀) hz hz₀
  let e := MulAut.conj k
  have hmap (x : G) : (core x).map e.toMonoidHom=core (e x) :=
    Theory.GroupTheory.map_centralizerResidualCore e x
  have hconj (a : G) : conjugate (core z) a=core (a⁻¹*z*a) := by
    have hh : (core z).map (MulAut.conj a⁻¹).toMonoidHom=core ((MulAut.conj a⁻¹) z) :=
      Theory.GroupTheory.map_centralizerResidualCore (MulAut.conj a⁻¹) z
    simpa only [conjugate,MulAut.conj_apply,inv_inv] using hh
  have hkC : k∈centralizer z := map_subtype_le _ hk
  have hkfix : e z=z := by
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hkC)
  have hI : (core z ⊓ conjugate (core z) g).map e.toMonoidHom =
      core z ⊓ conjugate (core z) g₀ := by
    rw [hconj,hconj,map_inf _ _ _ e.injective,hmap,hmap,hkfix]
    change core z ⊓ core (k*(g⁻¹*z*g)*k⁻¹)=_
    rw [he]
  rw [← hI,card_map_of_injective e.injective] at hc
  exact hc
end Theory.GroupTheory.Recognition.UnitaryFourThree.CentralizerHypothesis
