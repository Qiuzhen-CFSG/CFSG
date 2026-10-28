module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hyperplane fixers in binary subspace radicals

Fixing a hyperplane determines a linear actor by its displacement on one
complementary vector. If the actor belongs to the radical of a subspace P,
that displacement belongs to P, giving a bound of 2^dim(P). In particular,
a plane radical has at most four actors fixing a hyperplane pointwise.

Source application: Aschbacher–Smith, The Classification of Quasithin
Groups, 13.8.32(3), printed p.965. The geometric subspace and action are
retained, so no additional coordinate conjugator is needed.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite V]

/-- An actor in a subspace radical fixing a hyperplane is determined by
its displacement on one vector outside that hyperplane. -/
theorem radical_fixed_hyperplane_card_bound
    (P D : Submodule (ZMod 2) V)
    (hD : Module.finrank (ZMod 2) D + 1 = Module.finrank (ZMod 2) V)
    (A : Subgroup (GL V)) (hA : A ≤ radical P)
    (hfix : ∀ a : A, ∀ v ∈ D, a.val v = v) :
    Nat.card A ≤ 2 ^ Module.finrank (ZMod 2) P := by
  classical
  have hDt : D ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hD
    omega
  obtain ⟨v,_,hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hDt)
  have hspan : D ⊔ Submodule.span (ZMod 2) {v} = ⊤ := by
    apply (Submodule.sup_span_singleton_eq_top_iff hv).mpr
    have hd := D.finrank_quotient_add_finrank
    omega
  let f : A → P := fun a => ⟨a.val v-v,(hA a.property).2 v⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : a.val v = b.val v := (sub_left_inj).mp (congrArg Subtype.val hab)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have hw : w ∈ D ⊔ Submodule.span (ZMod 2) {v} := hspan ▸ Submodule.mem_top
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add,map_add,map_smul,map_smul,hfix a x hx,hfix b x hx,he]
  have hc := Nat.card_le_card_of_injective f hf
  rwa [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=P),Nat.card_zmod] at hc
end BinaryLinear
