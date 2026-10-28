module
public import Theory.GroupTheory.OrderedRootPresentation.Intertwining
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularPresentation

/-!
# The suffix after the first Suzuki root

The seven-root suffix inherits the native angular table and its unique ordered
coordinates. Its evaluation into any source requires only internal suffix
equations. The first root acts on this native suffix by conjugation; generation
by the main curve will extend the one remaining opposite-root identity.

Source: the positive-root collection in Steinberg §11 and Fong--Seitz II §10.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.AngularSuffix
open Subgroup Theory.GroupTheory OrderedRootPresentation CentralCovers.TwoPrimary
variable (m : ℕ)

abbrev suffixOrder := tail sourceOrder (.inr (0 : Fin 4))

theorem suffix_tail (i : PositiveTables.Root) (hi : i ≠ .inr 0) :
    tail suffixOrder i = tail sourceOrder i := by
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> first | exact (hi rfl).elim | rfl

theorem suffix_member (i : PositiveTables.Root) : i ∈ suffixOrder ↔ i ≠ .inr 0 := by
  cases i with
  | inl i => fin_cases i <;> simp [suffixOrder, tail, sourceOrder, sourceIndex]
  | inr i => fin_cases i <;> simp [suffixOrder, tail, sourceOrder, sourceIndex]

theorem suffix_nodup : suffixOrder.Nodup := by decide

private theorem word_cast {I : Type*} {R : I → Type*} {G : Type*} [Monoid G]
    (x : ∀ i, R i → G) {l k : List I} (h : l = k) (p : Tuple R k) :
    word R x l (cast (congrArg (Tuple R) h.symm) p) = word R x k p := by
  cases h
  rfl

def table : Table (AngularPresentation.Parameter m) suffixOrder where
  conjugate i j hj a b := by
    have hi : i ≠ .inr 0 := by
      intro he
      subst i
      simp [suffixOrder, tail, sourceOrder, sourceIndex] at hj
    have ht := suffix_tail i hi
    exact cast (congrArg (Tuple (AngularPresentation.Parameter m)) ht.symm)
      ((AngularPresentation.table m).conjugate i j (ht ▸ hj) a b)

theorem word_conjugate {G : Type*} [Group G]
    (x : ∀ i, AngularPresentation.Parameter m i →* G)
    (i j : PositiveTables.Root) (hj : j ∈ tail suffixOrder i)
    (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j)
    (hi : i ≠ .inr 0) :
    word (AngularPresentation.Parameter m) (fun k => x k) (tail suffixOrder i)
      ((table m).conjugate i j hj a b) =
    word (AngularPresentation.Parameter m) (fun k => x k) (tail sourceOrder i)
      ((AngularPresentation.table m).conjugate i j (suffix_tail i hi ▸ hj) a b) := by
  exact word_cast (fun k => x k) (suffix_tail i hi) _

theorem equations {G : Type*} [Group G]
    (x : ∀ i, AngularPresentation.Parameter m i →* G)
    (E : ∀ i j, i ≠ .inr 0 → ∀ hj a b,
      x i a * x j b * (x i a)⁻¹ =
        word (AngularPresentation.Parameter m) (fun k => x k) (tail sourceOrder i)
          ((AngularPresentation.table m).conjugate i j hj a b)) : Equations (table m) x := by
  intro i j hj a b
  have hi : i ≠ .inr 0 := by
    intro he
    subst i
    simp [suffixOrder, tail, sourceOrder, sourceIndex] at hj
  rw [word_conjugate m x i j hj a b hi]
  exact E i j hi _ a b

theorem native_equations : Equations (table m) (AngularPresentation.nativeRoot m) :=
  equations m _ (fun i j _ hj a b => AngularPresentation.native_equations m i j hj a b)

abbrev Carrier := join (AngularPresentation.Parameter m) (AngularPresentation.nativeRoot m) suffixOrder

def root (i : PositiveTables.Root) (hi : i ∈ suffixOrder) :
    AngularPresentation.Parameter m i →* Carrier m :=
  (AngularPresentation.nativeRoot m i).codRestrict _ (fun a =>
    range_le_join _ _ _ hi ⟨a,rfl⟩)

def realization {G : Type*} [Group G]
    (x : ∀ i, AngularPresentation.Parameter m i →* G) (E : Equations (table m) x) :
    Carrier m →* G :=
  OrderedRootPresentation.realization (table m) (native_equations m) E suffix_nodup
    (AngularPresentation.native_tail_injective m (.inr 0))

@[simp] theorem realization_root {G : Type*} [Group G]
    (x : ∀ i, AngularPresentation.Parameter m i →* G) (E : Equations (table m) x)
    (i : PositiveTables.Root) (hi : i ∈ suffixOrder) (a : AngularPresentation.Parameter m i) :
    realization m x E (root m i hi a) = x i a :=
  OrderedRootPresentation.realization_root (table m) (native_equations m) E suffix_nodup
    (AngularPresentation.native_tail_injective m (.inr 0)) i hi a

theorem realization_word {G : Type*} [Group G]
    (x : ∀ i, AngularPresentation.Parameter m i →* G) (E : Equations (table m) x)
    (p : Tuple (AngularPresentation.Parameter m) suffixOrder) :
    realization m x E
        ⟨word (AngularPresentation.Parameter m)
          (fun i => AngularPresentation.nativeRoot m i) suffixOrder p,
          word_mem_join _ _ _ _⟩ =
      word (AngularPresentation.Parameter m) (fun i => x i) suffixOrder p := by
  let r : join (AngularPresentation.Parameter m)
      (OrderedRootPresentation.rootHom (table m)) suffixOrder :=
    ⟨word (AngularPresentation.Parameter m)
        (fun i => OrderedRootPresentation.root (table m) i) suffixOrder p,
      word_mem_join _ _ _ _⟩
  have hr : OrderedRootPresentation.orderedEquiv (table m) (native_equations m)
      suffix_nodup (AngularPresentation.native_tail_injective m (.inr 0)) r =
      ⟨word (AngularPresentation.Parameter m)
          (fun i => AngularPresentation.nativeRoot m i) suffixOrder p,
        word_mem_join _ _ _ _⟩ := by
    apply Subtype.ext
    change OrderedRootPresentation.eval (table m) (native_equations m) r = _
    rw [OrderedRootPresentation.eval_word]
  rw [← hr]
  change OrderedRootPresentation.eval (table m) E
    ((OrderedRootPresentation.orderedEquiv (table m) (native_equations m)
      suffix_nodup (AngularPresentation.native_tail_injective m (.inr 0))).symm
      (OrderedRootPresentation.orderedEquiv (table m) (native_equations m)
        suffix_nodup (AngularPresentation.native_tail_injective m (.inr 0)) r)) = _
  rw [MulEquiv.symm_apply_apply, OrderedRootPresentation.eval_word]

def firstAction : AngularPresentation.Parameter m (.inr 0) →* MulAut (Carrier m) :=
  (Carrier m).normalizerMonoidHom.comp
    ((AngularPresentation.nativeRoot m (.inr 0)).codRestrict _ (fun a =>
      (AngularPresentation.native_equations m).normalizes (AngularPresentation.table m) (.inr 0) ⟨a,rfl⟩))

@[simp] theorem firstAction_val (a : AngularPresentation.Parameter m (.inr 0)) (v : Carrier m) :
    (firstAction m a v : Model m) = (a : Model m) * v * (a : Model m)⁻¹ := rfl

open ElementaryTwoBound.RootCalculations NormalizedRootCentralizers.CenterExponent

/-- The pure Suzuki curve generates each whole two-parameter root. -/
theorem main_generate (i : Fin 4) :
    closure (Set.range (fun t : CoefficientField m =>
      PositiveTables.rootChartEquiv m (.inr i) (t,0))) =
        (⊤ : Subgroup (AngularPresentation.Parameter m (.inr i))) := by
  rw [← Subgroup.map_subtype_inj, MonoidHom.map_closure,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  have he : (ElementaryTwoBound.X m (rootIndex (.inr i))).subtype ∘
      (fun t : CoefficientField m => PositiveTables.rootChartEquiv m (.inr i) (t,0)) =
      mainElement m (rootIndex (.inr i)) := by
    funext t
    change (PositiveTables.quartet m i t 0 : Model m) = _
    rw [PositiveTables.quartet_blockPoint, blockPoint, centralElement_zero, mul_one]
  rw [he]
  rfl

/-- Homomorphisms on the native suffix agree when they agree on its roots. -/
theorem hom_ext {G : Type*} [Group G] (f g : Carrier m →* G)
    (h : ∀ i (hi : i ∈ suffixOrder) a, f (root m i hi a) = g (root m i hi a)) : f = g := by
  have hle : Carrier m ≤ (f.eqLocus g).map (Carrier m).subtype := by
    apply join_le
    intro i hi
    rintro _ ⟨a,rfl⟩
    exact ⟨root m i hi a, h i hi a, rfl⟩
  apply MonoidHom.ext
  intro v
  obtain ⟨z,hz,he⟩ := hle v.property
  have hzv : z = v := Subtype.ext he
  subst z
  exact hz

/-- The main field curve in either kind of relative root. -/
def mainParameter : (i : PositiveTables.Root) → CoefficientField m → AngularPresentation.Parameter m i
  | .inl i, t => PositiveTables.rootChartEquiv m (.inl i) t
  | .inr i, t => PositiveTables.rootChartEquiv m (.inr i) (t,0)

/-- Every whole relative root is generated by its main field curve. -/
theorem root_main_generate (i : PositiveTables.Root) :
    closure (Set.range (mainParameter m i)) =
      (⊤ : Subgroup (AngularPresentation.Parameter m i)) := by
  cases i with
  | inr i => exact main_generate m i
  | inl i =>
    rw [← Subgroup.map_subtype_inj, MonoidHom.map_closure,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
    have he : (ElementaryTwoBound.X m (rootIndex (.inl i))).subtype ∘
        mainParameter m (.inl i) = mainElement m (rootIndex (.inl i)) := by
      funext t
      exact PositiveTables.pair_main i t
    rw [he]
    rfl

/-- Agreement on inverse-main actors and main suffix curves extends to the whole action. -/
theorem firstAction_intertwining {G : Type*} [Group G]
    (s : AngularPresentation.Parameter m (.inr 0) →* G) (f : Carrier m →* G)
    (h : ∀ (a : CoefficientField m) (i : PositiveTables.Root) (hi : i ∈ suffixOrder)
      (y : CoefficientField m),
      f (firstAction m (mainParameter m (.inr 0) a)⁻¹
        (root m i hi (mainParameter m i y))) =
        s (mainParameter m (.inr 0) a)⁻¹ * f (root m i hi (mainParameter m i y)) *
          (s (mainParameter m (.inr 0) a)⁻¹)⁻¹) :
    ∀ a v, f (firstAction m a v) = s a * f v * (s a)⁻¹ := by
  have hwhole (a : CoefficientField m) :
      (mainParameter m (.inr 0) a)⁻¹ ∈ intertwiningSubgroup (firstAction m) s f := by
    let A := (mainParameter m (.inr 0) a)⁻¹
    let F : Carrier m →* G := f.comp (firstAction m A).toMonoidHom
    let J : Carrier m →* G := (MulAut.conj (s A)).toMonoidHom.comp f
    have he : F = J := by
      apply hom_ext m
      intro i hi b
      have hr : F.comp (root m i hi) = J.comp (root m i hi) := by
        apply MonoidHom.eq_of_eqOn_dense (root_main_generate m i)
        rintro _ ⟨y,rfl⟩
        exact h a i hi y
      exact congrArg (fun z : AngularPresentation.Parameter m i →* G => z b) hr
    intro v
    exact congrArg (fun z : Carrier m →* G => z v) he
  apply intertwining_of_generators (firstAction m) s f
    (Set.range (mainParameter m (.inr 0))) (root_main_generate m (.inr 0))
  rintro _ ⟨a,rfl⟩
  have hi := (intertwiningSubgroup (firstAction m) s f).inv_mem (hwhole a)
  change mainParameter m (.inr 0) a ∈ intertwiningSubgroup (firstAction m) s f
  simpa only [inv_inv] using hi

end ReeF4.RootPresentationRecognition.AngularSuffix
