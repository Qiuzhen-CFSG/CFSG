module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.ComponentAction

/-!
# Component quotient actions from a local rank bound

The original common normalizer acts on the original component quotient.
Its kernel embeds in the component centralizer inside the chosen local
overgroup. Full cubic rank in that overgroup forces this centralizer to
have order prime to three. Thus the actual ambient quotient action inherits
the needed kernel bound without changing any quotient or Sylow marking.

Source application: N(D^x) in Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Four.RootNormalizerModel
open Theory.GroupAction.ComponentRankAction
variable {G : Type*} [Group G] [Finite G]

theorem component_sylow_quotient_action_in_overgroup
    (K N E : Subgroup G) [Group.IsPerfect K]
    (e : K ⧸ center K ≃* PSL) (P : Sylow 2 K)
    (hKE : K ≤ E) (hNE : N ≤ E)
    (hNK : N ≤ normalizer (K : Set G))
    (hNP : N ≤ normalizer ((P : Subgroup K).map K.subtype : Set G))
    (hZ : Nat.Coprime 3 (Nat.card (center K)))
    (hK : 2 ≤ primeRank 3 K) (hE : primeRank 3 E ≤ 2) :
    let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P₀ := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ α : N →* MulAut PSL,
      (∀ n k, α n (q k) = q (K.normalizerMonoidHom ⟨n, hNK n.property⟩ k)) ∧
      (∀ n, (P₀ : Subgroup PSL).map (α n).toMonoidHom = P₀) ∧
      Nat.Coprime 3 (Nat.card α.ker) := by
  let i : N →* normalizer (K : Set G) := inclusion hNK
  let α : N →* MulAut PSL := (action K e).comp i
  let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let P₀ := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hcompat (n : N) (k : K) :
      α n (q k) = q (K.normalizerMonoidHom ⟨n, hNK n.property⟩ k) :=
    MulAut.centralQuotientAction_apply e _ k
  refine ⟨α, hcompat, ?_, ?_⟩
  · intro n
    apply eq_of_le_of_card_ge
    · rintro u ⟨a, ha, rfl⟩
      change a ∈ (P : Subgroup K).map q at ha
      obtain ⟨k, hk, rfl⟩ := ha
      change α n (q k) ∈ (P : Subgroup K).map q
      rw [hcompat]
      apply mem_map_of_mem
      have hkG : (k : G) ∈ (P : Subgroup K).map K.subtype := mem_map_of_mem _ hk
      have hn := (mem_normalizer_iff.mp (hNP n.property) (k : G)).mp hkG
      obtain ⟨w, hw, he⟩ := hn
      exact (show w = K.normalizerMonoidHom ⟨n, hNK n.property⟩ k from Subtype.ext he) ▸ hw
    · rw [card_map_of_injective (α n).injective]
  · let K₀ := K.subgroupOf E
    let eK : K₀ ≃* K := subgroupOfEquivOfLe hKE
    have hz₀ : Nat.Coprime 3 (Nat.card (center K₀)) := by
      rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
      exact hZ
    have hr₀ : 2 ≤ primeRank 3 K₀ := by
      rw [primeRank_congr 3 eK]
      exact hK
    have hcop := centralizer_coprime K₀ hz₀ hr₀ hE
    let j : α.ker →* centralizer (K₀ : Set E) := {
      toFun a := ⟨⟨((a : N) : G), hNE (a : N).property⟩, by
        have ha : i (a : N) ∈ (action K e).ker := a.property
        rw [ker_eq] at ha
        intro k hk
        exact Subtype.ext (ha (k : G) hk)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : centralizer (K₀ : Set E) => ((t : E) : G)) hab
    exact hcop.coprime_dvd_right (card_dvd_of_injective j hj)

end Matrix.PSL3Four.RootNormalizerModel
