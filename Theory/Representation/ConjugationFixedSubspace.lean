module
public import Theory.Representation.ConjugationFixedQuotient
/-!
# Projected centralizers bound fixed quotients

A surjective linear projection from embedded coordinates gives a quotient
whose order is bounded by the centralizer index in any containing subgroup.
Only centralizing vectors must project to the specified fixed subspace; the
coordinate domain need not be invariant under the actor.

This supports the critical root hyperplane estimate in MS93 (3.4), p.868.
-/
public section
noncomputable section

open Subgroup
namespace Representation
variable {G W V : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem quotient_card_le_centralizer_index_of_projection
    (E A : Subgroup G) [Finite E] [Finite W]
    (j : Multiplicative W →* G) (hE : j.range ≤ E)
    (p : W →ₗ[ZMod 2] V) (hp : Function.Surjective p)
    (D : Submodule (ZMod 2) V)
    (hcentral : ∀ w, j (Multiplicative.ofAdd w) ∈ centralizer (A : Set G) → p w ∈ D) :
    Nat.card (V ⧸ D) ≤ (centralizer (A : Set G)).relIndex E := by
  let f : Multiplicative W →* Multiplicative (V ⧸ D) :=
    (D.mkQ.comp p).toAddMonoidHom.toMultiplicative
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := D.mkQ_surjective v.toAdd
    obtain ⟨u,hu⟩ := hp w
    refine ⟨Multiplicative.ofAdd u,?_⟩
    change Multiplicative.ofAdd (D.mkQ (p u)) = v
    rw [hu,hw,ofAdd_toAdd]
  have hker : (centralizer (A : Set G)).comap j ≤ f.ker := by
    intro w hw
    change D.mkQ (p w.toAdd) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hcentral _ hw)
  have hidx : f.ker.index = Nat.card (V ⧸ D) := by
    rw [index_ker,f.range_eq_top_of_surjective hf]
    exact Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative (V ⧸ D))) ≃* _).toEquiv
  rw [←hidx]
  calc
    f.ker.index ≤ ((centralizer (A : Set G)).comap j).index := by
      simpa only [relIndex_top_right] using
        (relIndex_le_of_le_left (L := (⊤ : Subgroup (Multiplicative W))) hker index_ne_zero_of_finite)
    _ = (centralizer (A : Set G)).relIndex j.range := index_comap _ _
    _ ≤ (centralizer (A : Set G)).relIndex E :=
      relIndex_le_of_le_right hE index_ne_zero_of_finite
end Representation
