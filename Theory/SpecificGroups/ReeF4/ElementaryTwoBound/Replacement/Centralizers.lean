module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers.Geometry

/-!
# The centralizer geometry for the Ree elementary replacement

Write every positive element as x₈(u)c with c in C. Since C centralizes V,
the relation y₃(a)x₈(u) = x₈(u)y₃(a)y₅(au) detects commutation in V.
For u nonzero this forces a = 0, leaving precisely the Y₅ line. Testing
y₃(1) also forces the literal eighth positive coordinate to vanish on C.
Together with the two-field-parameter plane this proves the four concrete
inputs to the first replacement step of GLS3 Lemma 3.3.9, printed p.135.
-/

public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.Replacement
open Subgroup Parabolics
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open CentralizerGeometry

private theorem central_eighth (m : ℕ) (a u : CoefficientField m) :
    centralElement m 2 a * mainElement m 7 u =
      mainElement m 7 u * centralElement m 2 a * centralElement m 4 (a * u) := by
  apply toSplitGroup_injective m
  simpa only [map_mul, mainElement_coe, centralElement_coe] using
    ReplacementCentralizerRoots.central_eighth m a u

private theorem central_four_eighth (m : ℕ) (b u : CoefficientField m) :
    Commute (centralElement m 4 b) (mainElement m 7 u) := by
  apply toSplitGroup_injective m
  simpa only [map_mul, mainElement_coe, centralElement_coe] using
    (ReplacementCentralizerRoots.main_central_4 m 7 u b).symm.eq

private theorem product_zero_of_commute (m : ℕ) (a u : CoefficientField m)
    (h : Commute (centralElement m 2 a) (mainElement m 7 u)) : a * u = 0 := by
  have he : centralElement m 4 (a * u) = 1 := by
    apply mul_left_cancel (a := mainElement m 7 u * centralElement m 2 a)
    rw [← central_eighth, mul_one, h.eq]
  apply centralElement_four_injective m
  simpa only [centralElement_zero] using he

private theorem commute_left_of_mul_right {G : Type*} [Group G] {a b c : G}
    (h : Commute a (b * c)) (hc : Commute a c) : Commute a b := by
  change a * b = b * a
  apply mul_right_cancel (b := c)
  simpa only [mul_assoc, hc.symm.eq] using h.eq

/-- The coordinate convention is exactly that of `PositiveParameters` and
`positiveWord`: the first pair parameter is the source eighth root. -/
theorem pair_eighth_eq_zero_of_mem_C (m : ℕ) (x : Model m) (hx : x ∈ C m)
    (p : PositiveParameters m) (hp : toSplitGroup m x = positiveWord m p) :
    p.pair 0 = 0 := by
  obtain ⟨c, hc⟩ := exists_C_factor_of_positiveWord m x p hp
  have hy : centralElement m 2 (1 : CoefficientField m) ∈ V m :=
    (show Y m 2 ≤ V m from le_sup_left) (subset_closure ⟨1, rfl⟩)
  have hxy : Commute (centralElement m 2 1) x := C_centralizes_V m hx _ hy
  have hcy : Commute (centralElement m 2 1) (c : Model m) :=
    C_centralizes_V m c.property _ hy
  rw [hc] at hxy
  simpa only [one_mul] using product_zero_of_commute m 1 (p.pair 0)
    (commute_left_of_mul_right hxy hcy)

/-- Outside C the centralizer in the actual root plane lies in Y₅. -/
theorem centralizer_V_outside_C (m : ℕ) (x : Model m) (hx : x ∈ unipotent m)
    (hxc : x ∉ C m) : V m ⊓ centralizer ({x} : Set (Model m)) ≤ Z m := by
  obtain ⟨u, c, rfl⟩ := exists_last_root_mul_C m x hx
  have hu : u ≠ 0 := by
    intro h
    apply hxc
    simpa only [h, mainElement_zero, one_mul] using c.property
  intro v hv
  obtain ⟨a, b, rfl⟩ := (mem_V_iff m v).mp hv.1
  have hc : Commute (centralElement m 4 b * centralElement m 2 a) (c : Model m) :=
    C_centralizes_V m c.property _ hv.1
  have h := commute_left_of_mul_right (show
      Commute (centralElement m 4 b * centralElement m 2 a)
        (mainElement m 7 u * (c : Model m)) from
      mem_centralizer_singleton_iff.mp hv.2) hc
  have ha : Commute (centralElement m 2 a) (mainElement m 7 u) := by
    change centralElement m 2 a * mainElement m 7 u =
      mainElement m 7 u * centralElement m 2 a
    apply mul_left_cancel (a := centralElement m 4 b)
    calc
      centralElement m 4 b * (centralElement m 2 a * mainElement m 7 u) =
          mainElement m 7 u * (centralElement m 4 b * centralElement m 2 a) := by
            simpa only [mul_assoc] using h.eq
      _ = centralElement m 4 b * (mainElement m 7 u * centralElement m 2 a) :=
        (central_four_eighth m b u).symm.left_comm _
  have ha0 := (mul_eq_zero.mp (product_zero_of_commute m a u ha)).resolve_right hu
  simp only [ha0, centralElement_zero, mul_one]
  exact subset_closure ⟨b, rfl⟩

/-- The concrete root calculations required by the source replacement.
They hold even at m = 0; the source's m ≥ 1 hypothesis is retained. -/
theorem centralizerCalculations (m : ℕ) (_hm : 1 ≤ m) : CentralizerCalculations m where
  elementary_V := CentralizerGeometry.elementary_V m
  centralizes := C_centralizes_V m
  outside := centralizer_V_outside_C m
  card_V := by rw [CentralizerGeometry.card_V, card_Z, pow_two]

end ReeF4.ElementaryTwoBound.Replacement
