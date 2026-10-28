module

public import Theory.Mathieu.M23.QuasithinGeometry.Design
public import Theory.Mathieu.M23.Properties.Transitivity

/-!
# The induced action on a four-set in M23

Four-transitivity realizes every permutation of a four-set by an element of
its setwise stabilizer. Unique heptad extension puts that element in the
heptad stabilizer as well. This gives the full symmetric action used after
Aschbacher--Smith, Lemma 5.2.19, printed p.656.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- Every permutation of a four-set is induced by a genuine M23 element
stabilizing that four-set. -/
theorem setAction_surjective {S : Finset (Fin 23)} (hS : S.card = 4) :
    Function.Surjective (setAction S) := by
  classical
  let e : Fin 4 ≃ S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  intro σ
  let a : Fin 4 ↪ Fin 23 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin 4 ↪ Fin 23 := (e.trans σ).toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp
    m23_isFourPretransitive) a b
  have happ (i : Fin 4) : g • (e i).val = (σ (e i)).val :=
    congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  have hact (z : S) : g • z.val = (σ z).val := by
    obtain ⟨i, rfl⟩ := e.surjective z
    exact happ i
  have hfix : g ∈ MulAction.stabilizer M23 S := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro z hz
    rw [hact ⟨z, hz⟩]
    exact (σ ⟨z, hz⟩).property
  refine ⟨⟨g, hfix⟩, ?_⟩
  apply Equiv.ext
  intro z
  exact Subtype.ext (hact z)

/-- In particular the chosen four-set supports the full symmetric action. -/
theorem lambda_action_surjective : Function.Surjective (setAction lambda) :=
  setAction_surjective lambda_card

/-- The symmetric action can also be realized inside the containing heptad
stabilizer, and the realization agrees pointwise with the natural action. -/
theorem exists_heptad_stabilizer_extension {S B : Finset (Fin 23)}
    (hS : S.card = 4) (hB : B ∈ m23Blocks) (hSB : S ⊆ B)
    (σ : Equiv.Perm S) :
    ∃ g : MulAction.stabilizer M23 B,
      (g : M23) ∈ MulAction.stabilizer M23 S ∧
        ∀ z : S, (g : M23) • z.val = (σ z).val := by
  obtain ⟨g, hg⟩ := setAction_surjective hS σ
  refine ⟨⟨g.val, four_stabilizer_le_heptad_stabilizer hS hB hSB g.property⟩,
    g.property, ?_⟩
  intro z
  exact congrArg Subtype.val (Equiv.congr_fun hg z)

end Sporadic.Mathieu.M23Geometry
