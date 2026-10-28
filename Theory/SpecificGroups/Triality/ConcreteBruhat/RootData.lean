module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRoots
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Triality.LeviTwistedDescent

/-!
# Folded root generators and Weyl words for genuine triality

The central node uses the q-Frobenius fixed field and the arm node uses the
cubic extension. The root elements are the actual elementary lifts of the
central Geck curve and the three commuting arm curves, with both signs.
Their characteristic-power identities survive the actual central quotient.

The proved pinned SL₂ maps transport two elementary matrix identities: the
Weyl word squares to one and exchanges the positive and negative curves.
Consequently adjoining all negative folded roots to the Borel is equivalent
to adjoining the single corresponding Weyl word. This does not assert that
the resulting subgroup is the entire root-defined parabolic; that equality
still needs the concrete Bruhat coverage argument.

Sources: GLS3 §§2.3–2.4 and Definition 2.6.4
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.11–12
(`refs/quasithin.pdf`). All results include q = 2.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Triality.Standard.ConcreteBruhat
open Parabolics ElementaryCentralKernel
noncomputable section

/-- The field of a folded simple root: cubic on the arms, fixed on the center. -/
abbrev RootField (P : Parameters) : Node → Type
  | .arms => ExtensionField P
  | .central => fixedField P

@[reducible] instance rootFieldField (P : Parameters) : (a : Node) → Field (RootField P a)
  | .arms => inferInstance
  | .central => inferInstance

/-- The signed folded root in the elementary graph-field fixed points. -/
def rootElementary (P : Parameters) (hp : P.prime = 2) (s : Bool) :
    (a : Node) → RootField P a → ElementaryGroup P
  | .arms, t => foldedElementary P hp s t
  | .central, t => centralElementary P s t.val t.property

/-- Its image in the actual central quotient. -/
def rootElement (P : Parameters) (hp : P.prime = 2) (s : Bool)
    (a : Node) (t : RootField P a) : Carrier P :=
  toCarrier P (rootElementary P hp s a t)

private def splitRankOneWith (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) :
    (a : Node) → SL(2, RootField P a) →* SplitGroup P
  | .arms => D.armsFixedEmbedding C
  | .central => (D.hom 1).comp
      (SpecialLinearGroup.map (fixedField P).subtype)

private theorem map_transvection {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single i j t) f = 1 + Matrix.single i j (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

private theorem splitRankOneWith_positive (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) (t : RootField P a) :
    splitRankOneWith P D C a (SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) t) = elementaryInclusion P (rootElementary P hp true a t) := by
  cases a with
  | central =>
    change D.hom 1 (SpecialLinearGroup.map (fixedField P).subtype
      (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) =
        positiveRoot P 1 t.val
    rw [map_transvection, D.positive]
    rfl
  | arms =>
    change D.hom 0 (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t) * D.hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) *
      D.hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t))) =
        positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
          positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t))
    simp only [map_transvection, D.positive]
    rfl
private theorem splitRankOneWith_negative (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) (t : RootField P a) :
    splitRankOneWith P D C a (SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) t) = elementaryInclusion P (rootElementary P hp false a t) := by
  cases a with
  | central =>
    change D.hom 1 (SpecialLinearGroup.map (fixedField P).subtype
      (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) =
        negativeRoot P 1 t.val
    rw [map_transvection, D.negative]
    rfl
  | arms =>
    change D.hom 0 (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t) * D.hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) *
      D.hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t))) =
        negativeRoot P 0 t * negativeRoot P 2 (fieldFrobenius P t) *
          negativeRoot P 3 (fieldFrobenius P (fieldFrobenius P t))
    simp only [map_transvection, D.negative]
    rfl
private abbrev upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev lower {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t
private def rankOneWeyl (F : Type*) [Field F] : SL(2, F) :=
  upper 1 * lower 1 * upper 1

private theorem rankOneWeyl_sq (F : Type*) [Field F] [CharP F 2] :
    rankOneWeyl F ^ 2 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeyl, upper, lower, pow_two, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]

private theorem rankOneWeyl_upper (F : Type*) [Field F] [CharP F 2] (t : F) :
    rankOneWeyl F * upper t * rankOneWeyl F = lower t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeyl, upper, lower, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]

private theorem rootField_charTwo (P : Parameters) (hp : P.prime = 2) (a : Node) :
    CharP (RootField P a) 2 := by
  let := rankOneExtensionCharTwo P hp
  cases a <;> dsimp [RootField] <;> infer_instance

/-- The characteristic-two rank-one Weyl word, before the central quotient. -/
def simpleElementary (P : Parameters) (hp : P.prime = 2) (a : Node) : ElementaryGroup P :=
  rootElementary P hp true a 1 * rootElementary P hp false a 1 *
    rootElementary P hp true a 1

/-- The concrete folded Weyl representative in the triality carrier. -/
def simpleRepresentative (P : Parameters) (hp : P.prime = 2) (a : Node) : Carrier P :=
  toCarrier P (simpleElementary P hp a)

private theorem splitRankOneWith_weyl (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) :
    splitRankOneWith P D C a (rankOneWeyl (RootField P a)) =
      elementaryInclusion P (simpleElementary P hp a) := by
  simp only [rankOneWeyl, map_mul, upper, lower, splitRankOneWith_positive P D C hp,
    splitRankOneWith_negative P D C hp, simpleElementary]

private theorem simpleElementary_relations (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) :
    simpleElementary P hp a ^ 2 = 1 ∧
      ∀ t, simpleElementary P hp a * rootElementary P hp true a t *
        simpleElementary P hp a = rootElementary P hp false a t := by
  let := rootField_charTwo P hp a
  have hinj : Function.Injective (elementaryInclusion P) :=
    fun _ _ h => Subtype.ext (Subtype.ext h)
  have hw := splitRankOneWith_weyl P D C hp a
  constructor
  · apply hinj
    calc
      elementaryInclusion P (simpleElementary P hp a ^ 2) =
          (elementaryInclusion P (simpleElementary P hp a)) ^ 2 := map_pow _ _ _
      _ = (splitRankOneWith P D C a (rankOneWeyl (RootField P a))) ^ 2 :=
        congrArg (fun x => x ^ 2) hw.symm
      _ = splitRankOneWith P D C a (rankOneWeyl (RootField P a) ^ 2) := (map_pow _ _ _).symm
      _ = splitRankOneWith P D C a 1 := congrArg _ (rankOneWeyl_sq (RootField P a))
      _ = elementaryInclusion P 1 := (map_one _).trans (map_one _).symm
  · intro t
    apply hinj
    let f := splitRankOneWith P D C a
    let w := rankOneWeyl (RootField P a)
    have hpos := splitRankOneWith_positive P D C hp a t
    have hneg := splitRankOneWith_negative P D C hp a t
    calc
      elementaryInclusion P (simpleElementary P hp a * rootElementary P hp true a t *
          simpleElementary P hp a) = elementaryInclusion P (simpleElementary P hp a) *
            elementaryInclusion P (rootElementary P hp true a t) *
              elementaryInclusion P (simpleElementary P hp a) := by simp only [map_mul]
      _ = f w * f (upper t) * f w :=
        congrArg₂ (· * ·) (congrArg₂ (· * ·) hw.symm hpos.symm) hw.symm
      _ = f (w * upper t) * f w := congrArg (fun x => x * f w) (map_mul f w (upper t)).symm
      _ = f (w * upper t * w) := (map_mul f _ _).symm
      _ = f (lower t) := congrArg f (rankOneWeyl_upper (RootField P a) t)
      _ = elementaryInclusion P (rootElementary P hp false a t) := hneg

/-- The Weyl word is already involutory before taking the central quotient. -/
theorem simpleElementary_sq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    simpleElementary P hp a ^ 2 = 1 :=
  (simpleElementary_relations P (pinnedRankOneMaps P hp) (armRootCommutation P hp) hp a).1

theorem simpleRepresentative_sq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    simpleRepresentative P hp a ^ 2 = 1 := by
  rw [simpleRepresentative, ← map_pow]
  exact (congrArg (toCarrier P) (simpleElementary_relations P
    (pinnedRankOneMaps P hp) (armRootCommutation P hp) hp a).1).trans (map_one _)

theorem simpleRepresentative_positive (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
    simpleRepresentative P hp a * rootElement P hp true a t *
      simpleRepresentative P hp a = rootElement P hp false a t := by
  simpa only [simpleRepresentative, rootElement, map_mul] using congrArg (toCarrier P)
    ((simpleElementary_relations P (pinnedRankOneMaps P hp)
      (armRootCommutation P hp) hp a).2 t)

theorem rootElement_pow_prime (P : Parameters) (hp : P.prime = 2) (s : Bool)
    (a : Node) (t : RootField P a) : rootElement P hp s a t ^ P.prime = 1 := by
  have h : rootElementary P hp s a t ^ P.prime = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    cases a with
    | arms => exact foldedRoot_pow_prime P hp s t
    | central => exact simpleRoot_pow_prime P s 1 t.val
  exact (map_pow (toCarrier P) _ _).symm.trans ((congrArg (toCarrier P) h).trans (map_one _))

theorem positive_mem_unipotent (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) : rootElement P hp true a t ∈ unipotent P := by
  refine ⟨rootElementary P hp true a t, ?_, rfl⟩
  cases a with
  | central => exact positiveRoot_mem_positiveSubgroup P 1 t.val
  | arms =>
    exact (positiveSubgroup P).mul_mem
      ((positiveSubgroup P).mul_mem (positiveRoot_mem_positiveSubgroup P 0 t)
        (positiveRoot_mem_positiveSubgroup P 2 (fieldFrobenius P t)))
      (positiveRoot_mem_positiveSubgroup P 3 (fieldFrobenius P (fieldFrobenius P t)))

theorem negative_mem_parabolic (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) : rootElement P hp false a t ∈ parabolic P a := by
  refine ⟨rootElementary P hp false a t, ?_, rfl⟩
  cases a with
  | central => exact negativeRoot_mem_splitParabolic P .central 1 (by rfl) t.val
  | arms =>
    exact (splitParabolic P .arms).mul_mem
      ((splitParabolic P .arms).mul_mem
        (negativeRoot_mem_splitParabolic P .arms 0 (by change (0 : Fin 4) ≠ 1; decide) t)
        (negativeRoot_mem_splitParabolic P .arms 2 (by change (2 : Fin 4) ≠ 1; decide) (fieldFrobenius P t)))
      (negativeRoot_mem_splitParabolic P .arms 3 (by change (3 : Fin 4) ≠ 1; decide)
        (fieldFrobenius P (fieldFrobenius P t)))

/-- All negative folded simple-root elements at the chosen node. -/
def negativeGenerators (P : Parameters) (hp : P.prime = 2) (a : Node) : Set (Carrier P) :=
  Set.range (rootElement P hp false a)

theorem negativeGenerators_pow_prime (P : Parameters) (hp : P.prime = 2) (a : Node)
    (g : Carrier P) (hg : g ∈ negativeGenerators P hp a) : g ^ P.prime = 1 := by
  obtain ⟨t, rfl⟩ := hg
  exact rootElement_pow_prime P hp false a t

theorem negativeGenerators_characteristic_power (P : Parameters) (hp : P.prime = 2)
    (a : Node) : ∀ g ∈ negativeGenerators P hp a, ∃ k : ℕ, g ^ (P.prime ^ k) = 1 := by
  intro g hg
  exact ⟨1, by simpa using negativeGenerators_pow_prime P hp a g hg⟩

theorem borel_sup_negativeGenerators_le (P : Parameters) (hp : P.prime = 2) (a : Node) :
    borel P ⊔ Subgroup.closure (negativeGenerators P hp a) ≤ parabolic P a := by
  refine sup_le (borel_le_parabolic P a) ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨t, rfl⟩
  exact negative_mem_parabolic P hp a t

theorem simpleRepresentative_eq_root_word (P : Parameters) (hp : P.prime = 2) (a : Node) :
    simpleRepresentative P hp a = rootElement P hp true a 1 *
      rootElement P hp false a 1 * rootElement P hp true a 1 := by
  exact (toCarrier P).map_mul _ _ |>.trans (congrArg
    (fun g => g * toCarrier P (rootElementary P hp true a 1)) ((toCarrier P).map_mul _ _))

/-- The SL₂ conjugation formula reduces the negative-root generating set to one Weyl word. -/
theorem borel_sup_negativeGenerators_eq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    borel P ⊔ Subgroup.closure (negativeGenerators P hp a) =
      borel P ⊔ Subgroup.closure {simpleRepresentative P hp a} := by
  apply le_antisymm
  · refine sup_le le_sup_left ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨t, rfl⟩
    rw [← simpleRepresentative_positive P hp a t]
    have hn : simpleRepresentative P hp a ∈
        borel P ⊔ Subgroup.closure {simpleRepresentative P hp a} :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
    have hx : rootElement P hp true a t ∈
        borel P ⊔ Subgroup.closure {simpleRepresentative P hp a} :=
      Subgroup.mem_sup_left (unipotent_le_borel P (positive_mem_unipotent P hp a t))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx) hn
  · refine sup_le le_sup_left ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    rw [simpleRepresentative_eq_root_word]
    have hx : rootElement P hp true a 1 ∈ borel P ⊔ Subgroup.closure (negativeGenerators P hp a) :=
      Subgroup.mem_sup_left (unipotent_le_borel P (positive_mem_unipotent P hp a 1))
    have hy : rootElement P hp false a 1 ∈ borel P ⊔ Subgroup.closure (negativeGenerators P hp a) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_range_self 1))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) hx

theorem simpleRepresentative_mem_parabolic (P : Parameters) (hp : P.prime = 2) (a : Node) :
    simpleRepresentative P hp a ∈ parabolic P a := by
  apply borel_sup_negativeGenerators_le P hp a
  rw [borel_sup_negativeGenerators_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

end
end Triality.Standard.ConcreteBruhat
