module
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# Exhausting a normal subgroup by two conjugacy classes

If the identity and two distinct nontrivial classes have total size equal
to a normal subgroup containing their representatives, they exhaust that
subgroup. This finite counting lemma keeps the literal ambient classes.
The binary unitary plane radical uses class sizes five and ten.
-/

open Subgroup
public noncomputable section
namespace Subgroup.ConjugacyClassCover
variable {G : Type*} [Group G] [Finite G]
theorem two_class_cover (Q : Subgroup G) [Q.Normal] (z t : G)
    (hzQ : z ∈ Q) (htQ : t ∈ Q) (hz : z ≠ 1) (ht : t ≠ 1)
    (hn : ¬ IsConj z t)
    (hc : 1 + Nat.card {x : G // IsConj z x} + Nat.card {x : G // IsConj t x} = Nat.card Q) :
    ∀ x ∈ Q, x = 1 ∨ IsConj z x ∨ IsConj t x := by
  let f : Unit ⊕ ({x : G // IsConj z x} ⊕ {x : G // IsConj t x}) → Q :=
    fun a => match a with
    | .inl _ => 1
    | .inr (.inl x) => ⟨x.val,by
        obtain ⟨g,hg⟩ := isConj_iff.mp x.property
        rw [← hg]
        exact (inferInstance : Q.Normal).conj_mem z hzQ g⟩
    | .inr (.inr x) => ⟨x.val,by
        obtain ⟨g,hg⟩ := isConj_iff.mp x.property
        rw [← hg]
        exact (inferInstance : Q.Normal).conj_mem t htQ g⟩
  have hf : Function.Injective f := by
    intro a b he
    have hv := congrArg Subtype.val he
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b =>
        cases b with
        | inl b =>
          change (1 : G) = b.val at hv
          exact False.elim (hz (isConj_one_left.mp (hv.symm ▸ b.property)))
        | inr b =>
          change (1 : G) = b.val at hv
          exact False.elim (ht (isConj_one_left.mp (hv.symm ▸ b.property)))
    | inr a =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          change a.val = (1 : G) at hv
          exact False.elim (hz (isConj_one_left.mp (hv ▸ a.property)))
        | inr b =>
          cases b with
          | inl b => exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext hv)
          | inr b =>
            change a.val = b.val at hv
            exact False.elim (hn (a.property.trans (hv.symm ▸ b.property.symm)))
      | inr a =>
        cases b with
        | inl b =>
          change a.val = (1 : G) at hv
          exact False.elim (ht (isConj_one_left.mp (hv ▸ a.property)))
        | inr b =>
          cases b with
          | inl b =>
            change a.val = b.val at hv
            exact False.elim (hn ((hv.symm ▸ b.property).trans a.property.symm))
          | inr b => exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext hv)
  have hcard : Nat.card (Unit ⊕ ({x : G // IsConj z x} ⊕ {x : G // IsConj t x})) = Nat.card Q := by
    simpa only [Nat.card_sum,Nat.card_unique,← Nat.add_assoc] using hc
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩).2
  intro x hx
  obtain ⟨a,ha⟩ := hs ⟨x,hx⟩
  have he := congrArg Subtype.val ha
  cases a with
  | inl a =>
    change (1 : G) = x at he
    exact Or.inl he.symm
  | inr a =>
    cases a with
    | inl a =>
      change a.val = x at he
      exact Or.inr (Or.inl (he ▸ a.property))
    | inr a =>
      change a.val = x at he
      exact Or.inr (Or.inr (he ▸ a.property))
end Subgroup.ConjugacyClassCover
