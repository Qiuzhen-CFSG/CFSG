module

public import CFSG.Quasithin.ChapterF.Section02
public import Mathlib.Data.ZMod.Basic

/-!
# The faithfulness gap in the printed F.2.11

Aschbacher--Smith, combined manuscript of 1 March 2004, pp. 268--269,
Lemma F.2.11(1),(3), claims that an extension into the automorphism group of
a completion is faithful. The stated hypotheses do not imply this.

Take the two-element chain, with vertex groups `1` and `C₂`, and let both
ambient groups and the completion group be `C₂`. The least vertex group is
trivial, so its conjugation action is trivial, its common centralizer inside
itself is trivial, and both factorization hypotheses hold. The inclusion
completion is faithful. Its composite with conjugation is trivial.

The same counterexample works for every nontrivial abelian group. The lemmas
below verify the individual source hypotheses and the failure of its conclusion.
In particular this obstruction is not a proposed replacement for F.2.11.
-/

public section

namespace CFSG.Quasithin.ChapterF.F211Obstruction

variable (G : Type*) [CommGroup G]

/-- The chain of subgroups `1 ≤ G`, serving as both `α` and `γ`. -/
def chain : YAmalgam Bool G where
  subgroup d := if d then ⊤ else ⊥
  le := by
    intro d e h
    cases d <;> cases e <;> simp_all
    cases Bool.eq_false_of_le_false h
  generated := by
    apply top_unique
    intro x _
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨true, by simp⟩)

@[simp] theorem chain_false : (chain G).subgroup false = ⊥ := by rfl
@[simp] theorem chain_true : (chain G).subgroup true = ⊤ := by rfl

/-- Hypothesis (a): `false` is the least vertex. -/
theorem least_vertex (d : Bool) : false ≤ d := Bool.false_le d

/-- Hypotheses (b),(c): the same subgroup diagram is used for `α` and `γ`,
so each `X_d` is normal in `Y_d`. Generation is part of `chain`. -/
theorem vertex_normal (d : Bool) :
    ((chain G).subgroup d |>.subgroupOf ((chain G).subgroup d)).Normal := by
  rw [Subgroup.subgroupOf_self]
  infer_instance

/-- The conjugation action of the least vertex group. -/
def action (_y : (chain G).subgroup false) : AmalgamAutomorphism (chain G).diagram :=
  AmalgamAutomorphism.refl

theorem action_is_conjugation (y : (chain G).subgroup false) (d : Bool)
    (x : (chain G).subgroup d) :
    ((action G y).map d x : G) = (y : G) * (x : G) * (y : G)⁻¹ := by
  simp only [action, AmalgamAutomorphism.refl_apply]
  simp

/-- Hypothesis (d), faithfulness of the inclusion completion. -/
theorem faithful : (chain G).completion.Faithful := (chain G).completion_faithful

/-- Hypothesis (d), stabilization of its equivalence class. -/
theorem stabilizes (y : (chain G).subgroup false) :
    Nonempty (CompletionEquivalence ((action G y).act (chain G).completion)
      (chain G).completion) := by
  change Nonempty (CompletionEquivalence (AmalgamAutomorphism.refl.act _)
    (chain G).completion)
  rw [AmalgamAutomorphism.act_refl]
  exact ⟨CompletionEquivalence.refl _⟩

/-- Hypothesis (e): the common centralizer *inside the least vertex group*
is trivial. -/
theorem common_centralizer :
    (chain G).subgroup false ⊓
      (⨅ d, Subgroup.centralizer ((chain G).subgroup d : Set G)) = ⊥ := by
  simp

/-- The product assertion of (f), expressed without pointwise-set notation. -/
theorem factorization (d : Bool) (z : G) :
    z ∈ (chain G).subgroup d ↔
      ∃ y ∈ (chain G).subgroup false, ∃ x ∈ (chain G).subgroup d, z = y * x := by
  constructor
  · intro hz
    exact ⟨1, (chain G).subgroup false |>.one_mem, z, hz, (one_mul z).symm⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    have hy1 : y = 1 := by simpa using hy
    simpa [hy1] using hx

/-- The intersection assertion of (f). -/
theorem intersection (d : Bool) :
    (chain G).subgroup false ⊓ (chain G).subgroup d = (chain G).subgroup false := by
  simp

/-- Conjugation kills every element of this completion. -/
theorem conjugation_trivial (g : G) : conjugationHom g = MulEquiv.refl G := by
  ext x
  rw [conjugationHom_apply]
  simp

/-- The restriction asserted to be faithful in F.2.11(3) is not injective at
the top vertex, contradicting (1) and (3) of the printed lemma. -/
theorem not_faithful_inner [Nontrivial G] :
    ¬ Function.Injective (fun x : (chain G).subgroup true =>
      conjugationHom ((chain G).completion.map true x)) := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hmem : g ∈ (chain G).subgroup true := by simp
  have heq := h (a₁ := ⟨g, hmem⟩) (a₂ := 1) (by simp only [conjugation_trivial])
  exact hg (congrArg Subtype.val heq)

/-- A finite example: the completion group may be cyclic of order two. -/
theorem cyclic_two_counterexample :
    ¬ Function.Injective
      (fun x : (chain (Multiplicative (ZMod 2))).subgroup true =>
        conjugationHom ((chain (Multiplicative (ZMod 2))).completion.map true x)) :=
  not_faithful_inner _

end CFSG.Quasithin.ChapterF.F211Obstruction
