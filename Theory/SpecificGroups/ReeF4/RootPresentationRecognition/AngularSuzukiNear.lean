module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularAdjacent

/-!
# Nearby whole-Suzuki angular equations

The checked main-curve exchange extends to both central parameters because
the neighboring Omega curves centralize the opposite root. Reflection then
gives the other two nearby pairs. Native coordinate uniqueness fixes the
explicit angular tails, with coefficient a*y even at q=2.

Source: GLS3 Table 2.4 and 2.4.5(d); Fong--Seitz II (10.8).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularSuzukiNear
open CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators
open Parabolics.RadicalCoordinates.FixedCoordinates SignedGeometry
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)
private theorem omega_eq (i : Fin 4) (b : CoefficientField m) :
    S i 0 b = centralElement m (![0,4,6,2] i) b := by
  rw [PositiveTables.quartet_blockPoint, blockPoint, mainElement_zero, one_mul]
  simp only [rootIndex, Sum.elim_inr, positive_quartet_indices]

private theorem main_eq (i : Fin 4) (a : CoefficientField m) :
    S i a 0 = mainElement m (![0,4,6,2] i) a := by
  rw [PositiveTables.quartet_blockPoint, blockPoint, centralElement_zero, mul_one]
  simp only [rootIndex, Sum.elim_inr, positive_quartet_indices]

private theorem pair_eq (i : Fin 4) (a : CoefficientField m) :
    L i a = mainElement m (![7,1,5,3] i) a := by
  rw [PositiveTables.pair_main]
  simp only [rootIndex, Sum.elim_inl, positive_pair_indices]

private theorem suzuki0_mem (a b : CoefficientField m) : S 0 a b ∈ ElementaryTwoBound.X m 0 := by
  have h := (PositiveTables.rootChartEquiv m (.inr 0) (a,b)).property
  change S 0 a b ∈ ElementaryTwoBound.X m (rootIndex (.inr 0)) at h
  simpa only [rootIndex, Sum.elim_inr,
    positive_quartet_indices, Matrix.cons_val_zero] using h

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

private theorem whole_central (i k : Fin 8) (b : CoefficientField m)
    (h : ∀ a, Commute (rootWord m i a) (centralWord m k b))
    (x : ElementaryTwoBound.X m i) : Commute (x : Model m) (centralElement m k b) := by
  have hle : ElementaryTwoBound.X m i ≤ centralizer {centralElement m k b} := by
    apply (closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (h a).eq
  exact mem_centralizer_singleton_iff.mp (hle x.property)


private theorem whole_shifted_omega (i : Fin 4) (hi : (![0,4,6,2] i : Fin 8) ≠ 7)
    (a b z : CoefficientField m) : Commute (S i a b) (S 3 0 z) := by
  rw [omega_eq]
  rw [PositiveTables.quartet_blockPoint]
  simp only [rootIndex,positive_quartet_indices]
  exact whole_central m _ 2 z
    (fun t => ReplacementCentralizerRoots.main_central_2 m _ hi t z)
    ⟨_,(mem_X_even m _ (by fin_cases i <;> decide) _).mpr ⟨a,b,rfl⟩⟩

private theorem simple_omega_shifted (b y z : CoefficientField m) :
    Commute (S 0 0 b) (S 3 y z) := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true)))
    (whole_shifted_omega m 1 (by decide) y z b).eq
  have h' : Commute (S 1 y z) (S 2 0 b) := by
    change _ * _ = _ * _
    simpa only [map_mul,quartet_reflect m true 1 (by decide),
      quartet_reflect m true 3 (by decide),next,Matrix.cons_val,Fin.isValue,
      Matrix.head_cons] using h
  have hh := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) h'.eq
  change _ * _ = _ * _
  simpa only [map_mul,quartet_reflect m false 1 (by decide),
    quartet_reflect m false 2 (by decide),next,Matrix.cons_val,Fin.isValue,
    Matrix.head_cons] using hh.symm

private theorem quartet_split (i : Fin 4) (a b : CoefficientField m) :
    S i a b = S i a 0 * S i 0 b := by
  rw [←Subgroup.coe_mul, PositiveTables.quartet_mul]
  simp only [add_zero,zero_add,mul_zero]

private theorem linear_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul]
  simp only [CharTwo.add_self_eq_zero,PositiveTables.pair_zero,Subgroup.coe_one]

private theorem conjugate_of_right {G : Type*} [Group G] {x y z : G}
    (h : x⁻¹*y⁻¹*x*y = z) (hx : Commute x z) (hy : Commute y z) :
    x*y*x⁻¹ = z*y := by
  have hs : x*y = y*x*z := by
    rw [←h]; group
  calc
    _ = (y*x*z)*x⁻¹ := by rw [hs]
    _ = (y*z*x)*x⁻¹ := by rw [mul_assoc y x z,hx.eq,←mul_assoc]
    _ = y*z := by group
    _ = z*y := hy.eq

private theorem main_near (a y : CoefficientField m) :
    S 0 a 0 * S 3 y 0 * (S 0 a 0)⁻¹ = L 1 (a*y) * S 3 y 0 := by
  have h : (S 0 a 0)⁻¹*(S 3 y 0)⁻¹*S 0 a 0*S 3 y 0 = L 1 (a*y) := by
    rw [main_eq,main_eq,pair_eq]
    exact Subtype.ext (TailRelations.BaseIntervals.rootWord_commutator_0_2 m a y)
  have h0 : Commute (S 0 a 0) (L 1 (a*y)) := by
    rw [main_eq,pair_eq]
    exact AngularAdjacent.native_adjacent_commute m 0 1 (by decide)
      ⟨_,mainElement_mem_X m 0 a⟩ ⟨_,mainElement_mem_X m 1 (a*y)⟩
  have h1 : Commute (S 3 y 0) (L 1 (a*y)) := by
    rw [main_eq,pair_eq]
    exact (AngularAdjacent.native_adjacent_commute m 1 2 (by decide)
      ⟨_,mainElement_mem_X m 1 (a*y)⟩ ⟨_,mainElement_mem_X m 2 y⟩).symm
  exact conjugate_of_right h h0 h1

/-- The full first nearby Suzuki equation, including the two central labels. -/
theorem near_conjugate (a b y z : CoefficientField m) :
    S 0 a b * S 3 y z * (S 0 a b)⁻¹ = L 1 (a*y) * S 3 y z := by
  have hc := simple_omega_shifted m b y z
  have hd := whole_shifted_omega m 0 (by decide) a 0 z
  calc
    _ = S 0 a 0 * (S 0 0 b * S 3 y z * (S 0 0 b)⁻¹) * (S 0 a 0)⁻¹ := by
      rw [quartet_split m 0 a b]; group
    _ = S 0 a 0 * S 3 y z * (S 0 a 0)⁻¹ := by rw [hc.eq]; group
    _ = (S 0 a 0*S 3 y 0*(S 0 a 0)⁻¹) *
        (S 0 a 0*S 3 0 z*(S 0 a 0)⁻¹) := by
      rw [quartet_split m 3 y z]; group
    _ = (L 1 (a*y)*S 3 y 0)*S 3 0 z := by
      rw [main_near,hd.eq]; simp only [mul_inv_cancel_right]
    _ = L 1 (a*y)*S 3 y z := by rw [quartet_split m 3 y z]; group

private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) (hz : z⁻¹ = z) : b*a*b⁻¹ = z*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = z⁻¹*a := by group
    _ = _ := by rw [hz]

/-- The terminal nearby Suzuki pair is the linear reflection of (0,2). -/
theorem near_terminal_conjugate (a b y z : CoefficientField m) :
    S 1 a b * S 2 y z * (S 1 a b)⁻¹ = L 2 (a*y) * S 2 y z := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false)))
    (near_conjugate m y z a b)
  have hh : S 2 y z * S 1 a b * (S 2 y z)⁻¹ = L 2 (a*y) * S 1 a b := by
    simpa only [map_mul,map_inv,quartet_reflect m false 0 (by decide),
      quartet_reflect m false 3 (by decide),pair_reflect m false 1 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_comm y a] using h
  exact reverse_conjugate hh (linear_inv m _ _)

/-- The middle nearby Suzuki pair retains the literal product coefficient. -/
theorem near_middle_conjugate (a b y z : CoefficientField m) :
    S 3 a b * S 1 y z * (S 3 a b)⁻¹ = L 3 (a*y) * S 1 y z := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true)))
    (near_terminal_conjugate m y z a b)
  have hh : S 1 y z * S 3 a b * (S 1 y z)⁻¹ = L 3 (a*y) * S 3 a b := by
    simpa only [map_mul,map_inv,quartet_reflect m true 1 (by decide),
      quartet_reflect m true 2 (by decide),pair_reflect m true 2 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_comm y a] using h
  exact reverse_conjugate hh (linear_inv m _ _)

open Theory.GroupTheory.OrderedRootPresentation

/-- The literal angular tail at positions 0 and 2. -/
def tail02 (a y z : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
  (PositiveTables.rootChartEquiv m (.inl 1) (a*y),PositiveTables.rootChartEquiv m (.inr 3) (y,z),1,1,1,1,1,PUnit.unit)

theorem tail02_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y z : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail02 m a y z) =
      f (.inl 1) (PositiveTables.rootChartEquiv m (.inl 1) (a*y)) * f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (y,z)) := by
  change f (.inl 1) (PositiveTables.rootChartEquiv m (.inl 1) (a*y)) * (f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (y,z)) * (f (.inl 3) 1 * (f (.inr 1) 1 * (f (.inl 2) 1 * (f (.inr 2) 1 * (f (.inl 0) 1 * (1))))))) = _
  simp only [map_one,mul_one]

/-- Native uniqueness identifies the chosen table with this field tuple. -/
theorem table02 (hj : (.inr 3 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a b y z : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 0) (.inr 3) hj
      (PositiveTables.rootChartEquiv m (.inr 0) (a,b))
      (PositiveTables.rootChartEquiv m (.inr 3) (y,z)) = tail02 m a y z := by
  apply AngularPresentation.conjugate_unique
  rw [tail02_word]
  exact near_conjugate m a b y z

/-- The literal angular tail at positions 2 and 4. -/
def tail24 (a y z : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 3)) :=
  (PositiveTables.rootChartEquiv m (.inl 3) (a*y),PositiveTables.rootChartEquiv m (.inr 1) (y,z),1,1,1,PUnit.unit)

theorem tail24_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y z : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail24 m a y z) =
      f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (a*y)) * f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (y,z)) := by
  change f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (a*y)) * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (y,z)) * (f (.inl 2) 1 * (f (.inr 2) 1 * (f (.inl 0) 1 * (1))))) = _
  simp only [map_one,mul_one]

/-- Native uniqueness identifies the chosen table with this field tuple. -/
theorem table24 (hj : (.inr 1 : PositiveTables.Root) ∈ tail sourceOrder (.inr 3))
    (a b y z : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 3) (.inr 1) hj
      (PositiveTables.rootChartEquiv m (.inr 3) (a,b))
      (PositiveTables.rootChartEquiv m (.inr 1) (y,z)) = tail24 m a y z := by
  apply AngularPresentation.conjugate_unique
  rw [tail24_word]
  exact near_middle_conjugate m a b y z

/-- The literal angular tail at positions 4 and 6. -/
def tail46 (a y z : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 1)) :=
  (PositiveTables.rootChartEquiv m (.inl 2) (a*y),PositiveTables.rootChartEquiv m (.inr 2) (y,z),1,PUnit.unit)

theorem tail46_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y z : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail46 m a y z) =
      f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (a*y)) * f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (y,z)) := by
  change f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (a*y)) * (f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (y,z)) * (f (.inl 0) 1 * (1))) = _
  simp only [map_one,mul_one]

/-- Native uniqueness identifies the chosen table with this field tuple. -/
theorem table46 (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 1))
    (a b y z : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 1) (.inr 2) hj
      (PositiveTables.rootChartEquiv m (.inr 1) (a,b))
      (PositiveTables.rootChartEquiv m (.inr 2) (y,z)) = tail46 m a y z := by
  apply AngularPresentation.conjugate_unique
  rw [tail46_word]
  exact near_terminal_conjugate m a b y z

end ReeF4.RootPresentationRecognition.AngularSuzukiNear
