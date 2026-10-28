module
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
public import Theory.Representation.BinaryPermutationSixCover.Facts
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# The five-dimensional moved core of a nonsingular point stabilizer

The two-point fixer acts as the alternating group on the six complementary
letters. Extending its even-weight core by zero identifies its image with
the full displacement span in the eight-letter core. The natural quotient
is injective on this subspace. Its constant six-letter vector projects to
the original nonsingular pair class.

The complement equivalence is the original ATLAS-derived pointFixerEquiv;
the coordinate action and quotient maps are retained literally.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
the paragraph preceding Lemma 12.6.6, printed p.824.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace BinaryPermutation.EightNonsingular

theorem complement_card (i j : Fin 8) (hij : i ≠ j) :
    Fintype.card (↑(({i,j} : Finset (Fin 8))ᶜ)) = 6 := by
  rw [Fintype.card_coe, Finset.card_compl]
  simp [hij]

def complementLetters (i j : Fin 8) (hij : i ≠ j) : Fin 6 ↪ Fin 8 :=
  (Fintype.equivFinOfCardEq (complement_card i j hij)).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem complementLetters_ne_left (i j : Fin 8) (hij : i ≠ j) (k : Fin 6) :
    complementLetters i j hij k ≠ i := by
  have h := ((Fintype.equivFinOfCardEq (complement_card i j hij)).symm k).property
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact h.1

theorem complementLetters_ne_right (i j : Fin 8) (hij : i ≠ j) (k : Fin 6) :
    complementLetters i j hij k ≠ j := by
  have h := ((Fintype.equivFinOfCardEq (complement_card i j hij)).symm k).property
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact h.2

theorem complementLetters_exhaust (i j : Fin 8) (hij : i ≠ j) (a : Fin 8)
    (hai : a ≠ i) (haj : a ≠ j) : ∃ k, complementLetters i j hij k = a := by
  let x : ↑(({i,j} : Finset (Fin 8))ᶜ) := ⟨a, by simp [hai,haj]⟩
  refine ⟨Fintype.equivFinOfCardEq (complement_card i j hij) x, ?_⟩
  exact congrArg Subtype.val ((Fintype.equivFinOfCardEq (complement_card i j hij)).symm_apply_apply x)

def extendSixFull (i j : Fin 8) (hij : i ≠ j) : Full (Fin 6) →ₗ[ZMod 2] Full (Fin 8) where
  toFun w := ∑ k, Pi.single (complementLetters i j hij k) (w k)
  map_add' w z := by simp only [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]
  map_smul' c w := by simp only [Pi.smul_apply, Pi.single_smul, Finset.smul_sum, RingHom.id_apply]

theorem extendSixFull_letter (i j : Fin 8) (hij : i ≠ j) (w : Full (Fin 6)) (k : Fin 6) :
    extendSixFull i j hij w (complementLetters i j hij k) = w k := by
  simp [extendSixFull, Pi.single_apply, (complementLetters i j hij).injective.eq_iff]

theorem extendSixFull_left (i j : Fin 8) (hij : i ≠ j) (w : Full (Fin 6)) :
    extendSixFull i j hij w i = 0 := by
  simp [extendSixFull, Ne.symm (complementLetters_ne_left i j hij _)]

theorem extendSixFull_right (i j : Fin 8) (hij : i ≠ j) (w : Full (Fin 6)) :
    extendSixFull i j hij w j = 0 := by
  simp [extendSixFull, Ne.symm (complementLetters_ne_right i j hij _)]

theorem augmentation_extendSixFull (i j : Fin 8) (hij : i ≠ j) (w : Full (Fin 6)) :
    augmentation (Fin 8) (extendSixFull i j hij w) = augmentation (Fin 6) w := by
  simp [extendSixFull, augmentation]

def extendSix (i j : Fin 8) (hij : i ≠ j) : core (Fin 6) →ₗ[ZMod 2] core (Fin 8) :=
  ((extendSixFull i j hij).comp (core (Fin 6)).subtype).codRestrict _ (by
    intro w
    change augmentation (Fin 8) (extendSixFull i j hij w.val) = 0
    rw [augmentation_extendSixFull]
    exact w.property)

theorem extendSix_injective (i j : Fin 8) (hij : i ≠ j) : Function.Injective (extendSix i j hij) := by
  intro w z h
  apply Subtype.ext
  funext k
  exact (extendSixFull_letter i j hij w.val k).symm.trans
    ((congrArg (fun v : core (Fin 8) => v.val (complementLetters i j hij k)) h).trans
      (extendSixFull_letter i j hij z.val k))

theorem range_extendSix (i j : Fin 8) (hij : i ≠ j) (w : core (Fin 8)) :
    w ∈ (extendSix i j hij).range ↔ w.val i = 0 ∧ w.val j = 0 := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨extendSixFull_left i j hij u.val, extendSixFull_right i j hij u.val⟩
  · intro hw
    let u : Full (Fin 6) := fun k => w.val (complementLetters i j hij k)
    have he : extendSixFull i j hij u = w.val := by
      funext a
      by_cases hai : a = i
      · subst a; exact (extendSixFull_left i j hij u).trans hw.1.symm
      by_cases haj : a = j
      · subst a; exact (extendSixFull_right i j hij u).trans hw.2.symm
      obtain ⟨k,rfl⟩ := complementLetters_exhaust i j hij a hai haj
      exact extendSixFull_letter i j hij u k
    have hu : u ∈ core (Fin 6) := by
      change augmentation (Fin 6) u = 0
      rw [← augmentation_extendSixFull i j hij, he]
      exact w.property
    exact ⟨⟨u,hu⟩, Subtype.ext he⟩

theorem toNatural_extendSix_injective (i j : Fin 8) (hij : i ≠ j) :
    Function.Injective ((coreToNatural (Fin 8)).comp (extendSix i j hij)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro w hw
  change coreToNatural (Fin 8) (extendSix i j hij w) = 0 at hw
  rcases (EightGeometry.coreToNatural_eq_zero _).mp hw with he | he
  · exact (extendSix_injective i j hij) (by simpa using Subtype.ext he)
  · have h := congrFun he i
    rw [show (extendSix i j hij w).val i = 0 from extendSixFull_left i j hij w.val] at h
    exact (zero_ne_one h).elim

theorem complementLetters_action (i j : Fin 8) (hij : i ≠ j)
    (g : pointFixer i j) (k : Fin 6) :
    complementLetters i j hij ((pointFixerEquiv i j hij g).val k) =
      g.val.val (complementLetters i j hij k) := by
  let e := Fintype.equivFinOfCardEq (complement_card i j hij)
  let g' : fixingSubgroup A (({i,j} : Finset (Fin 8)) : Set (Fin 8)) :=
    ⟨g.val, by simpa only [Finset.coe_insert, Finset.coe_singleton, pointFixer] using g.property⟩
  change (e.symm ((Atlas.Families.Alternating.relabel e
    (Atlas.Families.Alternating.stabilizerComplementEquiv {i,j} g')).val k)).val = _
  rw [Atlas.Families.Alternating.relabel_apply, e.symm_apply_apply]
  exact Atlas.Families.Alternating.stabilizerComplementEquiv_apply {i,j} g' (e.symm k)

theorem extendSix_equivariant (i j : Fin 8) (hij : i ≠ j)
    (g : pointFixer i j) (w : core (Fin 6)) :
    extendSix i j hij (alternatingCoreRepresentation (Fin 6) (pointFixerEquiv i j hij g) w) =
      alternatingCoreRepresentation (Fin 8) g.val (extendSix i j hij w) := by
  apply Subtype.ext
  funext a
  obtain ⟨a,rfl⟩ := g.val.val.surjective a
  change extendSixFull i j hij _ (g.val.val a) =
    extendSixFull i j hij w.val (g.val.val.symm (g.val.val a))
  rw [Equiv.symm_apply_apply]
  by_cases hai : a = i
  · subst a
    have hgi : g.val.val i = i := g.property ⟨i,Or.inl rfl⟩
    rw [hgi, extendSixFull_left, extendSixFull_left]
  by_cases haj : a = j
  · subst a
    have hgj : g.val.val j = j := g.property ⟨j,Or.inr rfl⟩
    rw [hgj, extendSixFull_right, extendSixFull_right]
  obtain ⟨k,rfl⟩ := complementLetters_exhaust i j hij a hai haj
  rw [← complementLetters_action, extendSixFull_letter, extendSixFull_letter]
  exact congrArg w.val ((pointFixerEquiv i j hij g).val.symm_apply_apply k)

/-- The literal displacement span for the two-point fixer is the six-letter core. -/
theorem pointFixer_moved_core (i j : Fin 8) (hij : i ≠ j) :
    Coinvariants.ker ((alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype) =
      (extendSix i j hij).range := by
  let ρ := (alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    apply (range_extendSix i j hij _).mpr
    have hgi : g.val.val.symm i = i := (g⁻¹).property ⟨i,Or.inl rfl⟩
    have hgj : g.val.val.symm j = j := (g⁻¹).property ⟨j,Or.inr rfl⟩
    change w.val (g.val.val.symm i) - w.val i = 0 ∧
      w.val (g.val.val.symm j) - w.val j = 0
    simp only [hgi,hgj,sub_self,and_self]
  · have h : Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤
        (Coinvariants.ker ρ).comap (extendSix i j hij) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,w⟩,rfl⟩
      change extendSix i j hij (_ - _) ∈ Coinvariants.ker ρ
      obtain ⟨a,rfl⟩ := (pointFixerEquiv i j hij).surjective g
      rw [map_sub,extendSix_equivariant]
      exact Coinvariants.sub_mem_ker a (extendSix i j hij w)
    rw [alternatingSix_core_generated] at h
    rintro _ ⟨w,rfl⟩
    exact h (Submodule.mem_top)

theorem finrank_pointFixer_moved_core (i j : Fin 8) (hij : i ≠ j) :
    Module.finrank (ZMod 2)
      (Coinvariants.ker ((alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype)) = 5 := by
  rw [pointFixer_moved_core i j hij, LinearMap.finrank_range_of_inj (extendSix_injective i j hij), finrank_core]
  rfl

/-- The constant six-letter word maps to the original nonsingular pair class. -/
theorem extendSix_constant_projection (i j : Fin 8) (hij : i ≠ j)
    (w : core (Fin 6)) (hw : w.val = allOne (Fin 6)) :
    coreToNatural (Fin 8) (extendSix i j hij w) = coreToNatural (Fin 8) (pair i j) := by
  apply sub_eq_zero.mp
  rw [← map_sub, EightGeometry.coreToNatural_eq_zero]
  right
  funext a
  by_cases hai : a = i
  · subst a
    change extendSixFull i j hij w.val i - (pair i j).val i = 1
    simp [extendSixFull_left,pair,hij]
  by_cases haj : a = j
  · subst a
    change extendSixFull i j hij w.val j - (pair i j).val j = 1
    simp [extendSixFull_right,pair,hij.symm]
  obtain ⟨k,rfl⟩ := complementLetters_exhaust i j hij a hai haj
  change extendSixFull i j hij w.val _ - (pair i j).val _ = 1
  rw [extendSixFull_letter,hw]
  simp [allOne,pair,hai,haj]

end BinaryPermutation.EightNonsingular
