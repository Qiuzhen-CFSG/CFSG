module

public import Theory.GroupTheory.SharpSetStabilizer
public import Theory.GroupTheory.Perm.S4SevenPointOrbits

/-!
# Complementary orbits of four-set stabilizers in degree eleven

In any sharply four-transitive action on eleven points, the setwise stabilizer
of a four-element set fixes a point outside that set and is transitive on the
six other points outside it.

Sharpness identifies the setwise stabilizer with the symmetric group on the
four-element set and bounds the total number of fixed points of every
nonidentity element by three. The seven-point symmetric-group orbit theorem
then gives the complementary orbits of sizes one and six. This proof uses only
the abstract sharp action, with no recognition or invariant-design hypothesis.

Source: Jordan's degree-eleven theorem, cited in Wong (1964), p. 108, and
Hall, *The Theory of Groups*, §5.8.1.
-/

open scoped Pointwise

namespace Theory.GroupTheory.MulAction

/-- The setwise stabilizer of any four-set in a sharply four-transitive
degree-eleven action has complementary orbits of sizes one and six. -/
public theorem IsSharplyMultiplyPretransitive.exists_fixed_point_and_transitive_fourSet_complement
    {G : Type*} [Group G] [Finite G] [MulAction G (Fin 11)]
    [FaithfulSMul G (Fin 11)]
    (h : IsSharplyMultiplyPretransitive G (Fin 11) 4)
    (s : Finset (Fin 11)) (hs : s.card = 4) :
    ∃ p, p ∉ s ∧ (∀ g : G, g • s = s → g • p = p) ∧
      ∀ q, q ∉ s → q ≠ p → ∀ r, r ∉ s → r ≠ p →
        ∃ g : G, g • s = s ∧ g • q = r := by
  classical
  have hA : Fintype.card (s : Set (Fin 11)) = 4 := by simpa using hs
  have hB : Fintype.card ↥((s : Set (Fin 11))ᶜ) = 7 := by
    change Fintype.card {x : Fin 11 // ¬x ∈ s} = 7
    rw [Fintype.card_subtype_compl]
    simpa using congrArg (fun k => 11 - k) hA
  obtain ⟨p, hp, ht⟩ := S4SevenPointOrbits.exists_fixed_point_and_transitive_complement
    hA hB (h.complementHom s hs) (h.complementHom_fixedPoints_lt s hs)
  refine ⟨p, p.property, ?_, ?_⟩
  · intro g hg
    have hgS : g • (s : Set (Fin 11)) = s := by
      rw [← Finset.coe_smul_finset, hg]
    let k : MulAction.stabilizer G (s : Set (Fin 11)) := ⟨g, hgS⟩
    have hp' := congrArg Subtype.val (hp (h.stabilizerEquivPerm s hs k))
    rw [h.complementHom_apply, MulEquiv.symm_apply_apply] at hp'
    exact hp'
  · intro q hq hqp r hr hrp
    obtain ⟨σ, hσ⟩ := ht ⟨q, hq⟩ (fun he => hqp (congrArg Subtype.val he))
      ⟨r, hr⟩ (fun he => hrp (congrArg Subtype.val he))
    let k := (h.stabilizerEquivPerm s hs).symm σ
    refine ⟨k, ?_, ?_⟩
    · apply Finset.coe_injective
      rw [Finset.coe_smul_finset]
      exact k.property
    · have he := congrArg Subtype.val hσ
      rw [h.complementHom_apply] at he
      exact he

end Theory.GroupTheory.MulAction
