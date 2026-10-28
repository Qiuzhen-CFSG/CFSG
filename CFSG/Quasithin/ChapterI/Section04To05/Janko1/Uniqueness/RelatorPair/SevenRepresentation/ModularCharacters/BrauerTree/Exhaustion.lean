module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularInput
public import Theory.Representation.PRegularSimpleCount

/-!
# Exhaustion from the fourteen eleven-regular conjugacy classes

The source table identifies the actual conjugacy classes of the arbitrary
source group. All except its order-eleven class are eleven-regular. Thus the
simple-module trace-independence bound permits at most fourteen pairwise
inequivalent irreducibles in characteristic eleven. Adjoining any omitted
irreducible to fourteen actual candidates would violate this bound.

This supplies completeness in the characteristic-eleven calculation described
in Gorenstein, *Finite Groups*, §16.6, p.482. The argument uses the literal
algebraic closure of GF(11) and actual intertwining equivalences. It requires
no semisimplicity of the group algebra or modular realization of an ordinary
character; constructing the fourteen candidates is a separate obligation.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

variable {G : Type*} [Group G] [Finite G]

/-- Exactly one of the fifteen source classes is eleven-singular. -/
public theorem OrdinaryData.card_elevenRegularClasses (d : OrdinaryData G) :
    Nat.card (ConjClasses.mk '' {g : G | ¬ 11 ∣ orderOf g}) = 14 := by
  have hmem (i : Fin 15) :
      d.classes i ∈ ConjClasses.mk '' {g : G | ¬ 11 ∣ orderOf g} ↔
        ¬ 11 ∣ classOrder i := by
    constructor
    · rintro ⟨g, hg, heq⟩
      rw [d.classes_eq] at heq
      obtain ⟨a, ha⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp heq)
      have ho : orderOf g = orderOf (d.representatives i) := by
        rw [← ha]
        exact ((MulAut.conj a).orderOf_eq g).symm
      simpa only [Set.mem_ofPred_eq, ho, d.orders] using hg
    · intro hi
      exact ⟨d.representatives i, by simpa only [Set.mem_ofPred_eq, d.orders] using hi,
        (d.classes_eq i).symm⟩
  let e := d.classes.subtypeEquiv fun i => (hmem i).symm
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

/-- Fourteen pairwise inequivalent actual irreducibles exhaust the coordinate
representations over the algebraic closure of GF(11). -/
public theorem OrdinaryData.equiv_of_fourteen_irreducibles (d : OrdinaryData G) (degree : Fin 14 → ℕ)
    (ρ : ∀ i, Representation ElevenClosure G (Fin (degree i) → ElevenClosure))
    (hρ : ∀ i, Representation.IsIrreducible (ρ i))
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (n : ℕ) (σ : Representation ElevenClosure G (Fin n → ElevenClosure))
    (hσ : Representation.IsIrreducible σ) :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  by_contra! hnone
  let M : Option (Fin 14) → Type := fun i =>
    match i with
    | none => Fin n → ElevenClosure
    | some j => Fin (degree j) → ElevenClosure
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module ElevenClosure (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation ElevenClosure G (M i) := fun i =>
    match i with
    | none => σ
    | some j => ρ j
  have finM : ∀ i, FiniteDimensional ElevenClosure (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, Representation.IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hσ
    | some j => exact hρ j
  have hpair : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some k => exact (hnone k).false φ
    | some k =>
      cases j with
      | none => exact (hnone k).false φ.symm
      | some l => exact (hne (fun h => hij (congrArg some h))).false φ
  have hb := Representation.irreducible_family_card_le_pRegularConjClasses M rep 11 hpair
  rw [d.card_elevenRegularClasses] at hb
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hb
  omega

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
