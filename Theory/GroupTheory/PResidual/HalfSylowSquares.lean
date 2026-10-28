module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Sylow

/-!
# Squares in half of a Sylow two-subgroup

If the two-residual has odd order, a Sylow two-subgroup maps isomorphically
to the residual quotient. Squares returning to that Sylow subgroup lie
in each of its index-two subgroups. This is the quotient calculation used
in Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem square_mem_half_sylow_of_odd_residual
    (P : Sylow 2 G) (K : Subgroup G)
    (hi : K.relIndex (P : Subgroup G) = 2)
    (hodd : Odd (Nat.card (pResidual 2 G))) (x : G)
    (hx : x ^ 2 ∈ (P : Subgroup G)) : x ^ 2 ∈ K := by
  let q := QuotientGroup.mk' (pResidual 2 G)
  let f := q.comp (P : Subgroup G).subtype
  have hmap : (P : Subgroup G).map q = ⊤ :=
    top_unique (((isPGroup_quotient_pResidual 2).to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a,ha,he⟩ := show y ∈ (P : Subgroup G).map q by rw [hmap]; trivial
    exact ⟨⟨a,ha⟩,he⟩
  have hdis : Disjoint (P : Subgroup G) (pResidual 2 G) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    exact disjoint_def.mp hdis a.property ((QuotientGroup.eq_one_iff _).mp ha)
  let e := MulEquiv.ofBijective f ⟨hinj,hsurj⟩
  let A := K.subgroupOf (P : Subgroup G)
  have hi' : (A.map e.toMonoidHom).index = 2 := by
    rw [index_map_of_bijective e.bijective]
    exact hi
  have hm := (A.map e.toMonoidHom).sq_mem_of_index_two hi' (q x)
  obtain ⟨a,ha,he⟩ := hm
  have he' : f a = f ⟨x ^ 2,hx⟩ := by
    change q (a:G) = q (x ^ 2)
    rw [map_pow]
    exact he
  change (⟨x ^ 2,hx⟩ : P) ∈ A
  rw [← hinj he']
  exact ha

end Theory.GroupTheory
