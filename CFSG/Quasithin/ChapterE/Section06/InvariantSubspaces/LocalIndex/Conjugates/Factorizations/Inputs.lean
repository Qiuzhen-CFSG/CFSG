module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Reduction

/-!
# Model calculations for the conjugate-block factorizations

The finite-group argument needs the order of the Baumann action, the order
of the action induced by the noncommuting conjugate module, and generation
by two conjugates in the quotient by the actual two-core. The centralizer
index inside the block module itself is already its defining quotient order;
the three constructors below discharge that part for each block type.

The remaining input predicates are unproved contracts. They assert neither
the factorizations nor a maximum elementary family or Frattini invariance.
In particular the alternating-five permutation module and the natural
module for `L₂(4)` retain different identifications.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6,
printed pp.156–157 (PDF pp.167–168); the preceding C.5.4 on p.155 and
the natural-module extension calculation I.2.3(1), printed p.413.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations

open Subgroup
universe u
variable {G : Type u} [Group G]

/-- The actual centralizer index is the order of the published module quotient. -/
theorem module_index (L : Subgroup G) :
    (centralizer (L : Set G)).relIndex (U L) = Nat.card (ChapterC.BlockModule L) := by
  have hc : (centralizer (L : Set G)).comap L.subtype = center L := by
    ext l
    change (∀ y ∈ L, y * (l : G) = (l : G) * y) ↔ l ∈ center L
    rw [mem_center_iff]
    constructor
    · intro hh y
      exact Subtype.ext (hh y y.property)
    · intro hh y hy
      exact congrArg Subtype.val (hh ⟨y, hy⟩)
  rw [U, ← relIndex_comap, hc]
  rfl

/-- The three numerical action facts used in the C.5.6 counting argument.
The conjugate index concerns the full module `U`, including its central layer. -/
structure ActionIndices (R L : Subgroup G) (x : G) (q : ℕ) : Prop where
  actor : (centralizer (U L : Set G)).relIndex (S R) = q
  conjugate : (centralizer (U L : Set G)).relIndex
    ((U L).map (MulAut.conj x).toMonoidHom) = q
  module : (centralizer (L : Set G)).relIndex (U L) = q * q

/-- The entire Sylow group preserves the single block's characteristic module. -/
theorem R_normalizes_U {K : GroupClass.{u}} {A H R L : Subgroup G}
    (h : Configuration K A H R L) : R ≤ normalizer (U L : Set G) :=
  (Chapter1.isSylowIn_iff.mp h.sylow).2.1.trans
    (h.normalizes_L.trans (normalizer_le_normalizer_characteristic_image L
      (ChapterC.blockU L)))

/-- Normality in the Sylow group is preserved by every allowed conjugator.
This is the normality needed to exclude the lone-transposition action in A₅. -/
theorem R_normalizes_conjugate {K : GroupClass.{u}} {A H R L : Subgroup G}
    (h : Configuration K A H R L) {x : G} (hx : x ∈ A) :
    R ≤ normalizer ((U L).map (MulAut.conj x).toMonoidHom : Set G) := by
  have hr : R.map (MulAut.conj x).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (h.normalizes_R hx)
  rw [← map_equiv_normalizer_eq, ← hr]
  exact map_mono (R_normalizes_U h)

/-- For an even-field natural block, only the two actor indices remain. -/
theorem actionIndices_of_l2 {R L : Subgroup G} {x : G} {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock L n)
    (hS : (centralizer (U L : Set G)).relIndex (S R) = 2 ^ n)
    (hx : (centralizer (U L : Set G)).relIndex
      ((U L).map (MulAut.conj x).toMonoidHom) = 2 ^ n) :
    ActionIndices R L x (2 ^ n) := by
  refine ⟨hS, hx, ?_⟩
  rw [module_index, hL.module_card, pow_mul, pow_two]

/-- The degree-three alternating module supplies the `q = 2` branch. -/
theorem actionIndices_of_a3 {R L : Subgroup G} {x : G}
    (hL : ChapterC.IsAlternatingBlock L 3)
    (hS : (centralizer (U L : Set G)).relIndex (S R) = 2)
    (hx : (centralizer (U L : Set G)).relIndex
      ((U L).map (MulAut.conj x).toMonoidHom) = 2) :
    ActionIndices R L x 2 := by
  refine ⟨hS, hx, ?_⟩
  rw [module_index, hL.module_card_odd (by decide)]
  rfl

/-- The degree-five permutation module supplies the `q = 4` branch. -/
theorem actionIndices_of_a5 {R L : Subgroup G} {x : G}
    (hL : ChapterC.IsAlternatingBlock L 5)
    (hS : (centralizer (U L : Set G)).relIndex (S R) = 4)
    (hx : (centralizer (U L : Set G)).relIndex
      ((U L).map (MulAut.conj x).toMonoidHom) = 4) :
    ActionIndices R L x 4 := by
  refine ⟨hS, hx, ?_⟩
  rw [module_index, hL.module_card_odd (by decide)]
  rfl

variable [Finite G]

/-- The natural and degree-three action calculation. The covering-module
fixed-space argument must be proved before this contract is supplied. -/
def NaturalIndicesInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 3) →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      ∃ q, ActionIndices R L x q

/-- The alternating-five calculation, including exclusion of a lone
transposition using the `R`-normality of both modules. It is required before
any factorization or Frattini-zero premise is available. -/
def AlternatingIndicesInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 5 →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      ActionIndices R L x 4

/-- Two conjugates generate the required block quotient. The earlier
Baumann span is an explicit premise, allowing this calculation to proceed
independently of its proof. The owner removes the two-core using relative
normality and two-perfection; literal generation is not assumed here. -/
def PairGenerationInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L →
        ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
          ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations

end
