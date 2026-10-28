module
public import Theory.GroupAction.ComponentRankAction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.Restriction

/-!
# The literal component and Sylow quotient action

The original normalizer action on K/Z(K) restricts to any subgroup preserving
K and its selected Sylow. Full cubic rank in a group of cubic rank at most
two makes the action kernel three-prime. Restriction to the actual projective
Sylow retains this property and supplies the UT₃(F₄) action used to construct
the common E₉. Every map keeps the original central quotient projection.

Source application: Aschbacher--Smith 2.5.7, printed p.556, within N(Dˣ).
-/
public section

open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Four.RootNormalizerModel
open Theory.GroupAction.ComponentRankAction
variable {H : Type*} [Group H] [Finite H]

/-- Restrict the actual component quotient action to a subgroup preserving
its actual Sylow. Rank discharges the three-prime action kernel. -/
theorem component_sylow_quotient_action
    (K N : Subgroup H) [Group.IsPerfect K]
    (e : K ⧸ center K ≃* PSL) (P : Sylow 2 K)
    (hNK : N ≤ normalizer (K : Set H))
    (hNP : N ≤ normalizer ((P : Subgroup K).map K.subtype : Set H))
    (hZ : Nat.Coprime 3 (Nat.card (center K)))
    (hK : 2 ≤ primeRank 3 K) (hH : primeRank 3 H ≤ 2) :
    let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P₀ := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ α : N →* MulAut PSL,
      (∀ n k, α n (q k) = q (K.normalizerMonoidHom ⟨n, hNK n.property⟩ k)) ∧
      (∀ n, (P₀ : Subgroup PSL).map (α n).toMonoidHom = P₀) ∧
      Nat.Coprime 3 (Nat.card α.ker) := by
  let i : N →* normalizer (K : Set H) := inclusion hNK
  let α : N →* MulAut PSL := (action K e).comp i
  let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let P₀ := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hcompat (n : N) (k : K) :
      α n (q k) = q (K.normalizerMonoidHom ⟨n, hNK n.property⟩ k) := by
    exact MulAut.centralQuotientAction_apply e _ k
  refine ⟨α, hcompat, ?_, ?_⟩
  · intro n
    apply eq_of_le_of_card_ge
    · rintro u ⟨a, ha, rfl⟩
      change a ∈ (P : Subgroup K).map q at ha
      obtain ⟨k, hk, rfl⟩ := ha
      change α n (q k) ∈ (P : Subgroup K).map q
      rw [hcompat]
      apply mem_map_of_mem
      have hkH : (k : H) ∈ (P : Subgroup K).map K.subtype := mem_map_of_mem _ hk
      have hn := (mem_normalizer_iff.mp (hNP n.property) (k : H)).mp hkH
      obtain ⟨w, hw, he⟩ := hn
      exact (show w = K.normalizerMonoidHom ⟨n, hNK n.property⟩ k from Subtype.ext he) ▸ hw
    · rw [card_map_of_injective (α n).injective]
  · have hc := kernel_coprime K e hZ hK hH
    apply hc.coprime_dvd_right
    change Nat.card ((action K e).comp i).ker ∣ Nat.card (action K e).ker
    rw [← MonoidHom.comap_ker]
    exact card_comap_dvd_of_injective _ i (inclusion_injective hNK)

/-- The constructed root action is compatible with the original component
quotient action on every element of the actual projective Sylow. -/
theorem component_root_action
    (K N : Subgroup H) [Group.IsPerfect K]
    (e : K ⧸ center K ≃* PSL) (P : Sylow 2 K)
    (hNK : N ≤ normalizer (K : Set H))
    (hNP : N ≤ normalizer ((P : Subgroup K).map K.subtype : Set H))
    (hZ : Nat.Coprime 3 (Nat.card (center K)))
    (hK : 2 ≤ primeRank 3 K) (hH : primeRank 3 H ≤ 2) :
    let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P₀ := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ eR : Root ≃* P₀, ∃ β : N →* MulAut Root,
      (∀ n u, (eR (β n u) : PSL) =
        action K e ⟨n, hNK n.property⟩ (eR u)) ∧
      Nat.Coprime 3 (Nat.card β.ker) := by
  let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P₀ := P.mapSurjective (f := q) hq
  obtain ⟨α, hcompat, hP, hk⟩ := component_sylow_quotient_action K N e P hNK hNP hZ hK hH
  obtain ⟨eR, β, hβ, hβk⟩ := exists_root_action α P₀ hP hk
  refine ⟨eR, β, ?_, hβk⟩
  intro n u
  rw [hβ]
  obtain ⟨k, he⟩ := hq (eR u)
  rw [← he, hcompat]
  exact (MulAut.centralQuotientAction_apply e _ k).symm
end Matrix.PSL3Four.RootNormalizerModel
