module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.PlaneTransport
public import Theory.Representation.BinaryOffender.Basic

/-!
# The four-group forced in the cyclic case

A subgroup of the radical of a marked two-space that fixes a hyperplane
embeds in that two-space by evaluation on one vector outside the hyperplane.
The embedding uses the actual linear action, so it gives an order bound on
the actor itself. A noncyclic elementary binary actor consequently has order
four. This is the group to which the middle-node obstruction must be applied.

The source's cyclic-case conclusion that D_H ∩ I is a fixed hyperplane is an
input here; the final cyclic contradiction still has to establish it and
transport the γ-to-α conjugator.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

local notation "Vec" => (Fin 4 → ZMod 2)

/-- Evaluation on a vector outside a fixed hyperplane embeds the actor in
the marked two-space. This gives the order-four bound in the cyclic case. -/
theorem card_le_four_of_plane_radical_and_fixed_hyperplane
    (P Q : Submodule (ZMod 2) Vec)
    (hP : Module.finrank (ZMod 2) P = 2) (hQ : Module.finrank (ZMod 2) Q = 3)
    (A : Subgroup (BinaryLinear.GL Vec)) (hrad : A ≤ BinaryLinear.radical P)
    (hfix : Q ≤ BinaryLinear.fixedSpace A) : Nat.card A ≤ 4 := by
  classical
  have hQt : Q ≠ ⊤ := by
    intro ht
    rw [ht, finrank_top] at hQ
    norm_num at hQ
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hQt)
  have hspan : Q ⊔ Submodule.span (ZMod 2) {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hv, hQ]
    simp
  let δ : A → P := fun a => ⟨(a : BinaryLinear.GL Vec) v - v, (hrad a.property).2 v⟩
  have hinj : Function.Injective δ := by
    intro a b hab
    have hev : (a : BinaryLinear.GL Vec) v = (b : BinaryLinear.GL Vec) v := by
      exact sub_left_injective (congrArg Subtype.val hab)
    apply Subtype.ext
    ext u
    have hu : u ∈ Q ⊔ Submodule.span (ZMod 2) {v} := hspan ▸ Submodule.mem_top
    obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [map_add, map_smul, hfix hq a a.property, hfix hq b b.property, hev]
  have hc : Nat.card P = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hP]
    decide
  exact (Nat.card_le_card_of_injective δ hinj).trans_eq hc

/-- For the source's noncyclic elementary actor the bound is sharp. The
conclusion is the actual order of the subgroup, needed by the middle-node
normal-four-group obstruction. -/
theorem card_eq_four_of_plane_radical_and_fixed_hyperplane
    (P Q : Submodule (ZMod 2) Vec)
    (hP : Module.finrank (ZMod 2) P = 2) (hQ : Module.finrank (ZMod 2) Q = 3)
    (A : Subgroup (BinaryLinear.GL Vec)) (hrad : A ≤ BinaryLinear.radical P)
    (hfix : Q ≤ BinaryLinear.fixedSpace A)
    (hA : Representation.BinaryOffender.IsElementaryTwo A)
    (hrank : 1 < Representation.BinaryOffender.rank A) : Nat.card A = 4 := by
  let : Finite (BinaryLinear.GL Vec) :=
    Finite.of_injective (fun g : BinaryLinear.GL Vec => (g : Vec → Vec)) DFunLike.coe_injective
  have hbound := card_le_four_of_plane_radical_and_fixed_hyperplane P Q hP hQ A hrad hfix
  have hcard := hA.card_eq_two_pow_rank
  have hlo : 4 ≤ Nat.card A := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
