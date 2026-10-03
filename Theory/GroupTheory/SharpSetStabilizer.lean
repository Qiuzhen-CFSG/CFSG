module

public import Theory.GroupTheory.SharpTransitivity
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Set stabilizers in sharply multiply transitive actions

In a sharply `n`-transitive action, fixing `n` distinct points forces an element
to be the identity. Consequently, a nonidentity element fixes fewer than `n`
points, and the setwise stabilizer of an `n`-element set induces its full
symmetric group, faithfully. The proofs use the unique transporter between
ordered tuples from `SharpTransitivity`.
-/

open scoped Pointwise

namespace Theory.GroupTheory.MulAction

variable {G α : Type*} [Group G] [MulAction G α] {n : ℕ}

/-- A group element fixing a full sharp tuple is the identity. -/
public theorem IsSharplyMultiplyPretransitive.eq_one_of_fixes_embedding
    (h : IsSharplyMultiplyPretransitive G α n) (x : Fin n ↪ α)
    {g : G} (hg : ∀ i, g • x i = x i) : g = 1 := by
  obtain ⟨a, _, ha⟩ := h.existsUnique_smul_eq x x
  have hg' : g • x = x := by ext i; exact hg i
  exact (ha g hg').trans (ha 1 (one_smul G x)).symm

/-- Fixing a set of the sharpness degree pointwise forces the identity. -/
public theorem IsSharplyMultiplyPretransitive.eq_one_of_fixes_finset
    (h : IsSharplyMultiplyPretransitive G α n) (s : Finset α) (hs : s.card = n)
    {g : G} (hg : ∀ a ∈ s, g • a = a) : g = 1 := by
  let e := (s.equivFinOfCardEq hs).symm
  exact h.eq_one_of_fixes_embedding (e.toEmbedding.trans (Function.Embedding.subtype _))
    (fun i => hg (e i) (e i).property)

/-- A nonidentity element in a sharp action fixes fewer points than the sharpness degree. -/
public theorem IsSharplyMultiplyPretransitive.card_fixedPoints_lt
    [Fintype α] [DecidableEq α]
    (h : IsSharplyMultiplyPretransitive G α n) {g : G} (hg : g ≠ 1) :
    (Finset.univ.filter (fun a : α => g • a = a)).card < n := by
  classical
  by_contra hn
  obtain ⟨s, hs, hsn⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  apply hg
  exact h.eq_one_of_fixes_finset s hsn (fun a ha => (Finset.mem_filter.mp (hs ha)).2)

/-- Restriction of the setwise stabilizer to a sharp set is bijective onto all permutations. -/
public theorem IsSharplyMultiplyPretransitive.bijective_stabilizer_toPermHom
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) :
    Function.Bijective (_root_.MulAction.toPermHom
      (_root_.MulAction.stabilizer G (s : Set α)) (s : Set α)) := by
  let e := (s.equivFinOfCardEq hs).symm
  let x : Fin n ↪ α := e.toEmbedding.trans (Function.Embedding.subtype _)
  constructor
  · intro g k hgk
    apply Subtype.ext
    obtain ⟨a, _, ha⟩ := h.existsUnique_smul_eq x (g.val • x)
    have hk : k.val • x = g.val • x := by
      ext i
      exact congrArg Subtype.val (Equiv.congr_fun hgk (e i)).symm
    exact (ha g.val rfl).trans (ha k.val hk).symm
  · intro σ
    let y : Fin n ↪ α :=
      (e.toEmbedding.trans σ.toEmbedding).trans (Function.Embedding.subtype _)
    obtain ⟨g, hg, _⟩ := h.existsUnique_smul_eq x y
    have hgs : ∀ a : s, g • (a : α) = (σ a : α) := by
      intro a
      have hi := congrArg (fun z : Fin n ↪ α => z (e.symm a)) hg
      simpa [x, y] using hi
    have hgS : g • (s : Set α) = s := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        change g • b ∈ s
        rw [hgs ⟨b, hb⟩]
        exact (σ ⟨b, hb⟩).property
      · intro ha
        refine ⟨σ.symm ⟨a, ha⟩, (σ.symm ⟨a, ha⟩).property, ?_⟩
        simpa using hgs (σ.symm ⟨a, ha⟩)
    refine ⟨⟨g, hgS⟩, ?_⟩
    ext a
    exact hgs a

/-- The setwise stabilizer of a sharp set is its full symmetric group. -/
public noncomputable def IsSharplyMultiplyPretransitive.stabilizerEquivPerm
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) :
    _root_.MulAction.stabilizer G (s : Set α) ≃* Equiv.Perm (s : Set α) :=
  MulEquiv.ofBijective (_root_.MulAction.toPermHom _ _)
    (h.bijective_stabilizer_toPermHom s hs)

/-- The stabilizer equivalence is given by the original action on points. -/
public theorem IsSharplyMultiplyPretransitive.stabilizerEquivPerm_apply
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n)
    (g : _root_.MulAction.stabilizer G (s : Set α)) (a : s) :
    (h.stabilizerEquivPerm s hs g a : α) = (g : G) • (a : α) := by
  unfold IsSharplyMultiplyPretransitive.stabilizerEquivPerm
  rfl

/-- The action of permutations of a sharp set on its complement, lifted through
its setwise stabilizer. -/
public noncomputable def IsSharplyMultiplyPretransitive.complementHom
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) :
    Equiv.Perm (s : Set α) →* Equiv.Perm ↥((s : Set α)ᶜ) :=
  (_root_.MulAction.toPermHom (_root_.MulAction.stabilizer G ((s : Set α)ᶜ))
    ↥((s : Set α)ᶜ)).comp
      ((MulEquiv.subgroupCongr (stabilizer_compl G α).symm).toMonoidHom.comp
        (h.stabilizerEquivPerm s hs).symm.toMonoidHom)

/-- Complementary permutations are given by the same lifted group element. -/
public theorem IsSharplyMultiplyPretransitive.complementHom_apply
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) (σ : Equiv.Perm (s : Set α))
    (a : ↥((s : Set α)ᶜ)) :
    (h.complementHom s hs σ a : α) =
      ((h.stabilizerEquivPerm s hs).symm σ : G) • (a : α) := by
  unfold IsSharplyMultiplyPretransitive.complementHom
  rfl

/-- The lift of a permutation has the prescribed action on the sharp set. -/
public theorem IsSharplyMultiplyPretransitive.stabilizerEquivPerm_symm_apply
    [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) (σ : Equiv.Perm (s : Set α)) (a : s) :
    ((h.stabilizerEquivPerm s hs).symm σ : G) • (a : α) = (σ a : α) := by
  rw [← h.stabilizerEquivPerm_apply s hs, MulEquiv.apply_symm_apply]

/-- The fixed points on a sharp set and its complement together number less than
 the sharpness degree for a nonidentity permutation of the set. -/
public theorem IsSharplyMultiplyPretransitive.complementHom_fixedPoints_lt
    [Fintype α] [DecidableEq α] (h : IsSharplyMultiplyPretransitive G α n)
    (s : Finset α) (hs : s.card = n) (σ : Equiv.Perm (s : Set α)) (hσ : σ ≠ 1) :
    (Finset.univ.filter (fun a : (s : Set α) => σ a = a)).card +
      (Finset.univ.filter (fun a : ↥((s : Set α)ᶜ) => h.complementHom s hs σ a = a)).card
      < n := by
  classical
  let g := (h.stabilizerEquivPerm s hs).symm σ
  have hg : (g : G) ≠ 1 := by
    intro hg
    have hg' : g = 1 := Subtype.ext hg
    apply hσ
    have heq := congrArg (h.stabilizerEquivPerm s hs) hg'
    simpa [g] using heq
  let t := Finset.univ.filter (fun a : α => (g : G) • a = a)
  have hleft : (Finset.univ.filter (fun a : (s : Set α) => σ a = a)).card =
      (t.filter (fun a => a ∈ s)).card := by
    apply Finset.card_bij (fun (a : (s : Set α)) _ => (a : α))
    · intro a ha
      have ha' := congrArg Subtype.val (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, t]
      exact ⟨(h.stabilizerEquivPerm_symm_apply s hs σ a).trans ha', a.property⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro a ha
      obtain ⟨ha, has⟩ := Finset.mem_filter.mp ha
      refine ⟨⟨a, has⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Subtype.ext
      exact (h.stabilizerEquivPerm_symm_apply s hs σ ⟨a, has⟩).symm.trans
        (Finset.mem_filter.mp ha).2
  have hright :
      (Finset.univ.filter (fun a : ↥((s : Set α)ᶜ) => h.complementHom s hs σ a = a)).card =
      (t.filter (fun a => a ∉ s)).card := by
    apply Finset.card_bij (fun (a : ↥((s : Set α)ᶜ)) _ => (a : α))
    · intro a ha
      have ha' := congrArg Subtype.val (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, t]
      exact ⟨(h.complementHom_apply s hs σ a).symm.trans ha', a.property⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro a ha
      obtain ⟨ha, has⟩ := Finset.mem_filter.mp ha
      refine ⟨⟨a, has⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Subtype.ext
      exact (h.complementHom_apply s hs σ ⟨a, has⟩).trans (Finset.mem_filter.mp ha).2
  rw [hleft, hright, Finset.card_filter_add_card_filter_not]
  exact h.card_fixedPoints_lt hg

end Theory.GroupTheory.MulAction
