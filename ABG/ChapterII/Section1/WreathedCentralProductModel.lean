module
public import ABG.ChapterII.Section1.WreathedQuaternionCore
public import Stellmacher.LaterDefs

/-!
# The canonical quaternion central product in a wreathed group

For a chosen wreathed presentation of height n ≥ 2, the subgroup V is the
central product of its quaternion core and the ambient cyclic center. This
is the fixed exceptional model used in ABG Chapter II §1 Lemma 3, article
p.10. The factors are the actual subgroups of S, so the existing
`Stellmacher.Later.IsCentralProductModel` predicate retains their embeddings
and avoids any choice of an unrelated abstract model.

The quaternion core has order eight and meets the center in order two.
The relative-index formula for a join with a normal subgroup therefore gives
|V| = 2^(n+2). Noncommutativity of the core passes to V, so the existing
wreathed subgroup-center theorem puts Z(V) in Z(S); the reverse inclusion is
immediate because V contains Z(S). Finally the two factors commute and their
intersection lies in Z(V), giving the central-product witness. The separate
coordinate module identifies this same V as <x₂,z>Z(S).
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem V_noncommutative :
    ¬ IsMulCommutative P.V := by
  intro h
  apply P.quaternion_core_noncommutative
  apply IsMulCommutative.of_comm
  intro a b
  apply Subtype.ext
  exact congrArg (fun v : P.V => (v : S))
    (h.is_comm.comm (⟨a, (show P.quaternionCore ≤ P.V from le_sup_left) a.property⟩ : P.V)
      (⟨b, (show P.quaternionCore ≤ P.V from le_sup_left) b.property⟩ : P.V))

private theorem center_le_V_center :
    Subgroup.center S ≤ (Subgroup.center P.V).map P.V.subtype := by
  intro c hc
  have hcV : c ∈ P.V := (show Subgroup.center S ≤ P.V from le_sup_right) hc
  refine ⟨⟨c, hcV⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro v
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (v : S))

public theorem V_center :
    (Subgroup.center P.V).map P.V.subtype = Subgroup.center S :=
  le_antisymm (P.nonabelian_center_le P.V P.V_noncommutative) P.center_le_V_center

public theorem card_V :
    Nat.card P.V = 2 ^ (n + 2) := by
  have hi : Nat.card (P.quaternionCore ⊓ Subgroup.center S : Subgroup S) *
      (Subgroup.center S).relIndex P.quaternionCore = Nat.card P.quaternionCore := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S)
        (P.quaternionCore ⊓ Subgroup.center S) P.quaternionCore bot_le inf_le_left
  rw [P.quaternion_core_structure.2.2, P.quaternion_core_structure.2.1] at hi
  have hi4 : (Subgroup.center S).relIndex P.quaternionCore = 4 := by omega
  have hv := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S)
    (Subgroup.center S) P.V bot_le (show Subgroup.center S ≤ P.V from le_sup_right)
  simp only [Subgroup.relIndex_bot_left, V, Subgroup.relIndex_sup_right] at hv
  rw [P.card_center, hi4] at hv
  calc
    Nat.card P.V = 2 ^ n * 4 := hv.symm
    _ = 2 ^ (n + 2) := by rw [pow_add]; norm_num

public theorem central_product_model :
    Stellmacher.Later.IsCentralProductModel P.V P.quaternionCore (Subgroup.center S) := by
  refine ⟨P.quaternionCore, Subgroup.center S, ⟨MulEquiv.refl _⟩, ⟨MulEquiv.refl _⟩,
    rfl, P.quaternion_core_structure.2.2, ?_, ?_⟩
  · intro b hb c hc
    exact Subgroup.mem_center_iff.mp hc b
  · exact inf_le_right.trans P.center_le_V_center

end ABG.Wreathed.Presentation
