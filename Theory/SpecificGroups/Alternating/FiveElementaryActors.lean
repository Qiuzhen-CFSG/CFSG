module

public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Elementary actors on a normal alternating group of degree five

The proved automorphism identification Aut(A₅) ≃ S₅ and the dihedral Sylow
calculation bound elementary two-subgroups of Aut(A₅) by four. For an actual
normal A₅ in an ambient finite group, the kernel of conjugation is its literal
centralizer. Thus an elementary actor disjoint from that centralizer has
order at most four; the ambient group need not act faithfully on A₅.

This is the automizer bound used to exclude the marked natural SL₂(4)
component in Aschbacher–Smith 13.7.13, printed p.942. The automorphism theorem
is GLS3, Theorem 5.2.1. The lower bound from the source chief factors remains
a separate input of the chapter consumer.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveExtensionAction

/-- The full automorphism group of A₅ has elementary two-rank at most two. -/
theorem automorphism_primeRank_two_le :
    primeRank 2 (MulAut (alternatingGroup (Fin 5))) ≤ 2 := by
  rw [← primeRank_equiv 2 symmetricAutEquiv]
  exact Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two

/-- Every elementary two-subgroup of the actual automorphism group has order at most four. -/
theorem elementary_card_le_four (E : Subgroup (MulAut (alternatingGroup (Fin 5))))
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 :=
  (primeRank_le_iff_elementary_card_le _).mp automorphism_primeRank_two_le E inferInstance

/-- The literal centralizer intersection is precisely the faithfulness needed for the actor. -/
theorem elementary_card_le_four_of_disjoint {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (eK : K ≃* alternatingGroup (Fin 5))
    (E : Subgroup H) [IsElementaryAbelian 2 E]
    (hd : Disjoint E (centralizer (K : Set H))) : Nat.card E ≤ 4 := by
  let f : H →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal
  have hf : Function.Injective (f.comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    have hc : (x : H) ∈ centralizer (K : Set H) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      change MulAut.conjNormal (x : H) = 1
      apply (MulAut.congr eK).injective
      rw [map_one]
      exact hx
    have hxC : (x : H) ∈ E ⊓ centralizer (K : Set H) := ⟨x.property, hc⟩
    rwa [disjoint_iff.mp hd, mem_bot] at hxC
  have hEA : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map f
  let := hEA
  have hb := elementary_card_le_four (E.map f)
  have he := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [MonoidHom.range_comp, range_subtype] at he
  exact he.trans_le hb

end Theory.SpecificGroups.Alternating.FiveExtensionAction
