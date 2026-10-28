module

public import Theory.GroupAction.OddInvariantSylowConjugacy.Ambient

/-!
# Fixed conjugators into a specified ambient invariant Sylow subgroup

The target Sylow subgroup may already have been chosen by another part of
the argument. Transporting its given ambient normalizer condition to the
subgroup action permits the fixed-conjugator theorem to use that exact
Sylow. No new existential choice of Sylow is made.

Source application: GLS IV, Chapter 2, Proposition 16.5, transporting the
two marked torus witnesses into the same Sylow used by the Frattini argument.
-/

namespace Theory.GroupAction
open Subgroup

/-- Every invariant p-subgroup embeds into the specified invariant Sylow
by an ambient conjugator centralizing the complete actor group. -/
public theorem exists_ambient_fixed_conjugator_le_chosen_sylow
    {G : Type*} [Group G] [Finite G]
    (H A : Subgroup G) (hodd : Odd (Nat.card H))
    (hA : IsPGroup 2 A) (hAH : A ≤ normalizer H)
    {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hAP : A ≤ normalizer ((P : Subgroup H).map H.subtype))
    (Q : Subgroup G) (hQH : Q ≤ H) (hQp : IsPGroup p Q)
    (hAQ : A ≤ normalizer Q) :
    ∃ c : H, (c : G) ∈ centralizer (A : Set G) ∧
      Q.map (MulAut.conj (c : G)).toMonoidHom ≤ (P : Subgroup H).map H.subtype := by
  let : MulDistribMulAction A H := conjMulDistribMulActionOfLeNormalizer A H hAH
  have hmem (x : H) : x ∈ (P : Subgroup H) ↔
      (x : G) ∈ (P : Subgroup H).map H.subtype := by
    constructor
    · exact fun hx => ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact (Subtype.ext he : y=x) ▸ hy
  have hPI : IsInvariant A H (P : Subgroup H) := by
    refine ⟨fun a x => ?_⟩
    rw [hmem,hmem]
    exact mem_normalizer_iff.mp (hAP a.property) _
  have hQI : IsInvariant A H (Q.subgroupOf H) := by
    refine ⟨fun a x => ?_⟩
    change (x : G)∈Q ↔ (a : G)*(x : G)*(a : G)⁻¹∈Q
    exact mem_normalizer_iff.mp (hAQ a.property) _
  obtain ⟨c,hcf,hle⟩ := exists_fixed_conjugator_le_invariant_sylow hA hodd
    (Q.subgroupOf H) (hQp.of_equiv (subgroupOfEquivOfLe hQH).symm) hQI P hPI
  refine ⟨c,?_,?_⟩
  · intro a ha
    have he := congrArg Subtype.val (hcf ⟨a,ha⟩)
    change a*(c : G)*a⁻¹=c at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨c*(⟨x,hQH hx⟩ : H)*c⁻¹,
      hle (mem_map_of_mem _ (show (⟨x,hQH hx⟩ : H)∈Q.subgroupOf H from hx)),rfl⟩

end Theory.GroupAction
