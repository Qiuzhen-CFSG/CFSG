module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.SectionData
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Support

/-!
# Counting the supported Ree section parameters

Each of the six sections in GLS3 Lemma 3.3.9 has an explicit space of free
parameters. The coordinate maps below are bijections onto the stated support
predicates. Together with a supported factorization of the literal subgroup,
they give its order by the already proved injectivity of positive words.
The factorization premise is separate from this counting argument.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations.Sections
open NormalizedRootCentralizers.CenterExponent

/-- The six literal subgroup joins appearing in the source counting argument. -/
inductive Kind | d | d1 | d2 | t1 | t2 | k
  deriving DecidableEq

def subgroup (m : ℕ) : Kind → Subgroup (Model m)
  | .d => D m
  | .d1 => D₁ m
  | .d2 => D₂ m
  | .t1 => T₁ m
  | .t2 => T₂ m
  | .k => K m

def Supported {m : ℕ} (s : Kind) (p : PositiveParameters m) : Prop :=
  match s with
  | .d => DSupport p
  | .d1 => D₁Support p
  | .d2 => D₂Support p
  | .t1 => T₁Support p
  | .t2 => T₂Support p
  | .k => KSupport p

abbrev dimension : Kind → ℕ
  | .d => 9
  | .d1 => 7
  | .d2 => 7
  | .t1 => 5
  | .t2 => 5
  | .k => 8

/-- Insert the free scalars into the existing pair/main/central layout. -/
def pack (m : ℕ) : (s : Kind) → (Fin (dimension s) → CoefficientField m) →
    PositiveParameters m
  | .d, v => ⟨![0, v 0, v 1, v 2], ![0, v 3, 0, v 4], ![v 5, v 6, v 7, v 8]⟩
  | .d1, v => ⟨![0, v 0, 0, v 1], ![0, v 2, 0, v 3], ![v 4, v 5, 0, v 6]⟩
  | .d2, v => ⟨![0, 0, v 0, v 1], ![0, v 2, 0, v 3], ![0, v 4, v 5, v 6]⟩
  | .t1, v => ⟨![0, v 0, 0, v 1], ![0, 0, 0, 0], ![v 2, v 3, 0, v 4]⟩
  | .t2, v => ⟨![0, 0, v 0, v 1], ![0, 0, 0, 0], ![0, v 2, v 3, v 4]⟩
  | .k, v => ⟨![0, v 0, v 1, v 2], ![0, v 3, 0, v 4], ![v 5, v 6, 0, v 7]⟩

/-- Read precisely the coordinates not required to vanish. -/
def unpack (m : ℕ) : (s : Kind) → PositiveParameters m →
    (Fin (dimension s) → CoefficientField m)
  | .d, p => ![p.pair 1, p.pair 2, p.pair 3, p.main 1, p.main 3, p.central 0, p.central 1, p.central 2, p.central 3]
  | .d1, p => ![p.pair 1, p.pair 3, p.main 1, p.main 3, p.central 0, p.central 1, p.central 3]
  | .d2, p => ![p.pair 2, p.pair 3, p.main 1, p.main 3, p.central 1, p.central 2, p.central 3]
  | .t1, p => ![p.pair 1, p.pair 3, p.central 0, p.central 1, p.central 3]
  | .t2, p => ![p.pair 2, p.pair 3, p.central 1, p.central 2, p.central 3]
  | .k, p => ![p.pair 1, p.pair 2, p.pair 3, p.main 1, p.main 3, p.central 0, p.central 1, p.central 3]

theorem pack_supported (m : ℕ) (s : Kind) (v : Fin (dimension s) → CoefficientField m) :
    Supported s (pack m s v) := by
  cases s <;> simp [Supported, pack, DSupport, D₁Support, D₂Support,
    T₁Support, T₂Support, KSupport]

theorem unpack_pack (m : ℕ) (s : Kind) (v : Fin (dimension s) → CoefficientField m) :
    unpack m s (pack m s v) = v := by
  cases s <;> funext i <;> fin_cases i <;> rfl

theorem pack_unpack (m : ℕ) (s : Kind) (p : PositiveParameters m)
    (hp : Supported s p) : pack m s (unpack m s p) = p := by
  cases p with
  | mk pair main central =>
    cases s <;>
      simp only [Supported, DSupport, D₁Support, D₂Support, T₁Support,
        T₂Support, KSupport] at hp <;>
      simp only [pack, unpack] <;>
      congr 1 <;> funext i <;> fin_cases i <;> simp_all

/-- All supported coordinate words belong to the corresponding literal join. -/
theorem word_mem (m : ℕ) (s : Kind) (p : PositiveParameters m)
    (hp : Supported s p) : wordElement m p ∈ subgroup m s := by
  cases s with
  | d => exact wordElement_mem_D m p hp
  | d1 => exact wordElement_mem_D₁ m p hp
  | d2 => exact wordElement_mem_D₂ m p hp
  | t1 => exact wordElement_mem_T₁ m p hp
  | t2 => exact wordElement_mem_T₂ m p hp
  | k => exact wordElement_mem_K m p hp

/-- Counting the free parameters requires only the forward factorization;
reverse membership and uniqueness have already been proved. -/
theorem card_section (m : ℕ) (s : Kind)
    (h : ∀ x ∈ subgroup m s, ∃ p : PositiveParameters m,
      Supported s p ∧ wordElement m p = x) :
    Nat.card (subgroup m s) = (2 ^ (2 * m + 1)) ^ dimension s := by
  let f : (Fin (dimension s) → CoefficientField m) → subgroup m s :=
    fun v => ⟨wordElement m (pack m s v), word_mem m s _ (pack_supported m s v)⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    have hp := wordElement_injective m (congrArg Subtype.val hvw)
    simpa only [unpack_pack] using congrArg (unpack m s) hp
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨p, hp, he⟩ := h x x.property
    refine ⟨unpack m s p, Subtype.ext ?_⟩
    change wordElement m (pack m s (unpack m s p)) = x.val
    rw [pack_unpack m s p hp, he]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_fun,
    Nat.card_fin, field_card]

end ReeF4.ElementaryTwoBound.RootCalculations.Sections
