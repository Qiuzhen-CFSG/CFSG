module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients

/-!
# Completion of the short mixed angular family

The Suzuki reflection transports positions (1,4) to the reversed terminal
pair. Reversing conjugation and using the Omega involution law gives the
literal (4,7) relation. The coefficient is a*y for all fields, including q=2.
Native coordinate uniqueness then fixes the three-slot angular tail.

Source: Fong--Seitz II, Section 10, (10.11)(i) and its Weyl transforms;
GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularShortCompletion
open CentralCovers.TwoPrimary SignedGeometry
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)
private theorem pair_reflect (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (reflection m (NormalizerPresentation.side s)) (L i a) = L (next false s i) a := by
  have hh := SignedCharts.reflection_pair m s (true,i) a
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  exact hh

private theorem quartet_reflect (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (reflection m (NormalizerPresentation.side s)) (S i a b) = S (next true s i) a b := by
  have hh := SignedCharts.reflection_quartet m s (true,i) a b
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  exact hh


private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) : b*a*b⁻¹ = z⁻¹*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = _ := by group

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,PositiveTables.quartet_zero,Subgroup.coe_one]


/-- The last short mixed angular relation, at positions 4 and 7. -/
theorem short_terminal_conjugate (a b y : CoefficientField m) :
    S 1 a b * L 0 y * (S 1 a b)⁻¹ = S 2 0 (a*y) * L 0 y := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true)))
    (AngularCoefficients.short_perpendicular_conjugate m a b y)
  have hh : L 0 y * S 1 a b * (L 0 y)⁻¹ = S 2 0 (a*y) * S 1 a b := by
    simpa only [map_mul,map_inv,pair_reflect m true 1 (by decide),
      quartet_reflect m true 1 (by decide),quartet_reflect m true 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [omega_inv] using reverse_conjugate hh

open Theory.GroupTheory.OrderedRootPresentation

/-- The angular tail has one nonzero Omega correction and the last linear root. -/
def tail47 (a y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 1)) :=
  (1,PositiveTables.rootChartEquiv m (.inr 2) (0,a*y),
    PositiveTables.rootChartEquiv m (.inl 0) y,PUnit.unit)

theorem tail47_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail47 m a y) =
      f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (0,a*y)) *
        f (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) y) := by
  change f (.inl 2) 1 *
    (f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (0,a*y)) *
      (f (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) y) * 1)) = _
  simp only [map_one,one_mul,mul_one]

/-- Native coordinate uniqueness fixes this literal table entry. -/
theorem table47 (hj : (.inl 0 : PositiveTables.Root) ∈ tail sourceOrder (.inr 1))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 1) (.inl 0) hj
      (PositiveTables.rootChartEquiv m (.inr 1) (a,b))
      (PositiveTables.rootChartEquiv m (.inl 0) y) = tail47 m a y := by
  apply AngularPresentation.conjugate_unique
  rw [tail47_word]
  exact short_terminal_conjugate m a b y

end ReeF4.RootPresentationRecognition.AngularShortCompletion
