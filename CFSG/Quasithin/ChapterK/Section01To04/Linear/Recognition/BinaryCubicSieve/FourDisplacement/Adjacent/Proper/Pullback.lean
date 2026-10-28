module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Contracts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Pulling proper adjacent actors back to the component

For an actor contained in the actual SL₄ image, take its inverse image under
`componentEmbedding`. Faithfulness preserves elementary rank and nontriviality;
the equality of the original linear operators preserves cubicity and the common
fixed space. Membership of each conjugate of the adjacent central root also
pulls back literally, retaining the remaining-actor clause.

This transport is used by `Adjacent.Proper` after the graph-actor exclusion.
It proves no displacement estimate on its own.

Source: the inner/outer distinction in Guralnick–Malle, Classification of
2F-modules II, author manuscript, Propositions 4.7–4.8, pp.25–28;
Aschbacher–Smith K.3.2, pp.454–455.
-/

public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Proper

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Pullback along the literal component embedding preserves all actor data,
including the exclusion of conjugates of the adjacent central root. -/
theorem inner_actor_pullback (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hin : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ))
    (hc : IsCubic (normalizerRepresentation σ) A)
    (hr : RemainingAdjacentActor σ A) :
    ∃ B : Subgroup Group,
      IsElementaryTwo B ∧ IsCubic σ B ∧ rank B = rank A ∧
      fixedCodim σ B = fixedCodim (normalizerRepresentation σ) A ∧
      (2 ≤ rank B ∨ ∀ c : Group, c * adjacentCentralRoot 0 1 * c⁻¹ ∉ B) ∧
      B.map (componentEmbedding σ) = A := by
  let : IsElementaryAbelian 2 A := hA.2
  let j := componentEmbedding σ
  have hj : Function.Injective j := by
    intro x y he
    exact hf (congrArg (fun z : linearNormalizer σ => z.val.val) he)
  let B := A.comap j
  have hm : B.map j = A := by
    apply le_antisymm (map_comap_le _ _)
    intro t ht
    obtain ⟨x, hx⟩ := hin ht
    have hjx : j x = t := Subtype.ext hx
    exact ⟨x, show j x ∈ A from hjx.symm ▸ ht, hjx⟩
  have hB : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hj
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply hj
      change j ((x : Group) ^ 2) = j 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (j x) x.property }
  have hnontrivial : B ≠ ⊥ := by
    intro hb
    apply hA.1
    rw [← hm, hb, Subgroup.map_bot]
  have hrank : rank B = rank A := by rw [← hm, rank_map_injective j hj]
  refine ⟨B, ⟨hnontrivial, hB⟩, ?_, hrank, ?_, ?_, hm⟩
  · intro a ha b hb c hc' v
    exact hc (j a) ha (j b) hb (j c) hc' v
  · have he := fixedCodim_map_equivariant σ (normalizerRepresentation σ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) B
    rwa [hm] at he
  · rcases hr with hr | hr
    · exact Or.inl (by simpa only [hrank] using hr)
    · exact Or.inr hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Proper
