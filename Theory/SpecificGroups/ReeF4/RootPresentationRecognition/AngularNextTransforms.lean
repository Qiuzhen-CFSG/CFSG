module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularLinearCommute

/-!
# Nonadjacent next-linear transforms and the extreme linear angular pair

Reflecting the established whole-root next-linear action, then reversing
conjugation, gives angular positions (1,6) and (2,7). Inversion reverses the
three correction factors into precisely the angular order. Each linear and
Omega factor is an involution, so both central coefficients survive unchanged,
including at field two. Native coordinate uniqueness identifies the literal
table entries; no source comparison is used.

The second-eighth right commutator supplies positions (1,7). Its two
linear correction factors commute with the endpoints and therefore collect
directly into their angular order.

Source: Fong--Seitz II, Section 10, (10.13)(i), (10.15); GLS3 Table 2.4 and
2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
open CentralCovers.TwoPrimary
open NormalizedRootCentralizers.CenterExponent
namespace ReeF4.RootPresentationRecognition.AngularNextTransforms
open CentralCovers.TwoPrimary SignedGeometry
open Parabolics.RadicalCoordinates.FixedCoordinates
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

private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul]
  simp only [CharTwo.add_self_eq_zero,PositiveTables.pair_zero,Subgroup.coe_one]

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,PositiveTables.quartet_zero,Subgroup.coe_one]

/-- Angular positions 1 and 6: reflection and reversal put all three correction
factors in angular order, including both binary central coefficients. -/
theorem next_reflected_conjugate (a b y : CoefficientField m) :
    L 1 y * S 2 a b * (L 1 y)⁻¹ =
      S 3 0 (a*titsEnd m y) * L 3 (titsEnd m a*y) *
        S 1 0 ((b+titsEnd m a*a)*y) * S 2 a b := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) (AngularCoefficients.next_conjugate m a b y)
  have hh : S 2 a b * L 1 y * (S 2 a b)⁻¹ =
      (S 1 0 ((b+titsEnd m a*a)*y) * L 3 (titsEnd m a*y) *
        S 3 0 (a*titsEnd m y)) * L 1 y := by
    simpa only [map_mul,map_inv,quartet_reflect m false 0 (by decide),quartet_reflect m false 3 (by decide),
      quartet_reflect m false 1 (by decide),pair_reflect m false 2 (by decide),pair_reflect m false 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [mul_inv_rev,omega_inv,pair_inv,mul_assoc] using reverse_conjugate hh

/-- Angular positions 2 and 7: a second reflection and reversal retain the
same parameters and place the two Omega corrections on opposite sides. -/
theorem next_shifted_conjugate (a b y : CoefficientField m) :
    S 3 a b * L 0 y * (S 3 a b)⁻¹ =
      S 1 0 ((b+titsEnd m a*a)*y) * L 2 (titsEnd m a*y) *
        S 2 0 (a*titsEnd m y) * L 0 y := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true))) (next_reflected_conjugate m a b y)
  have hh : L 0 y * S 3 a b * (L 0 y)⁻¹ =
      (S 2 0 (a*titsEnd m y) * L 2 (titsEnd m a*y) *
        S 1 0 ((b+titsEnd m a*a)*y)) * S 3 a b := by
    simpa only [map_mul,map_inv,quartet_reflect m true 2 (by decide),quartet_reflect m true 3 (by decide),
      quartet_reflect m true 1 (by decide),pair_reflect m true 1 (by decide),pair_reflect m true 3 (by decide),
      next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  simpa only [mul_inv_rev,omega_inv,pair_inv,mul_assoc] using reverse_conjugate hh


open Theory.GroupTheory.OrderedRootPresentation

/-- Explicit angular tail for positions 1 and 6, including both Omega corrections. -/
def tail16 (a b y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inl 1)) :=
  ((PositiveTables.rootChartEquiv m (.inr 3) (0,a*titsEnd m y)), (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)), (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)), 1, (PositiveTables.rootChartEquiv m (.inr 2) (a,b)), 1, PUnit.unit)

theorem tail16_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail16 m a b y) =
      f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*titsEnd m y)) * f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)) * f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)) * f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) := by
  change f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*titsEnd m y)) * (f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)) * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)) * (f (.inl 2) 1 * (f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) * (f (.inl 0) 1 * (1)))))) = _
  simp only [map_one,one_mul,mul_one,mul_assoc]

/-- Uniqueness fixes these coefficients in the literal native angular table. -/
theorem table16 (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inl 1))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inl 1) (.inr 2) hj
      (PositiveTables.rootChartEquiv m (.inl 1) y) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) = tail16 m a b y := by
  apply AngularPresentation.conjugate_unique
  rw [tail16_word]
  exact next_reflected_conjugate m a b y

/-- Explicit angular tail for positions 2 and 7, including both Omega corrections. -/
def tail27 (a b y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 3)) :=
  (1, (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)), (PositiveTables.rootChartEquiv m (.inl 2) (titsEnd m a*y)), (PositiveTables.rootChartEquiv m (.inr 2) (0,a*titsEnd m y)), (PositiveTables.rootChartEquiv m (.inl 0) y), PUnit.unit)

theorem tail27_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail27 m a b y) =
      f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)) * f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (titsEnd m a*y)) * f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (0,a*titsEnd m y)) * f (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) y) := by
  change f (.inl 3) 1 * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,(b+titsEnd m a*a)*y)) * (f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (titsEnd m a*y)) * (f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (0,a*titsEnd m y)) * (f (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) y) * (1))))) = _
  simp only [map_one,one_mul,mul_one,mul_assoc]

/-- Uniqueness fixes these coefficients in the literal native angular table. -/
theorem table27 (hj : (.inl 0 : PositiveTables.Root) ∈ tail sourceOrder (.inr 3))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 3) (.inl 0) hj
      (PositiveTables.rootChartEquiv m (.inr 3) (a,b)) (PositiveTables.rootChartEquiv m (.inl 0) y) = tail27 m a b y := by
  apply AngularPresentation.conjugate_unique
  rw [tail27_word]
  exact next_shifted_conjugate m a b y

private theorem conjugate_from_commutator {G : Type*} [Group G]
    {a b c d : G}
    (hc : a⁻¹ * b⁻¹ * a * b = c * d)
    (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    a * b * a⁻¹ = c * d * b := by
  have hswap : a * b = b * a * (c * d) := by
    calc
      a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a * (c * d) := by rw [hc]
  calc
    a * b * a⁻¹ = b * a * (c * d) * a⁻¹ := by rw [hswap]
    _ = b * (c * d) := by
      calc
        b * a * (c * d) * a⁻¹ = b * (a * c) * d * a⁻¹ := by group
        _ = b * (c * a) * d * a⁻¹ := by rw [hac.eq]
        _ = b * c * (a * d) * a⁻¹ := by group
        _ = b * c * (d * a) * a⁻¹ := by rw [had.eq]
        _ = b * (c * d) := by group
    _ = c * d * b := by
      calc
        b * (c * d) = (b * c) * d := by group
        _ = (c * b) * d := by rw [hbc.eq]
        _ = c * (b * d) := by group
        _ = c * (d * b) := by rw [hbd.eq]
        _ = c * d * b := by group

private theorem pair_main (i : Fin 4) (a : CoefficientField m) :
    L i a = mainElement m (![7,1,5,3] i) a := by
  rw [PositiveTables.pair_main]
  simp only [rootIndex, Sum.elim_inl, positive_pair_indices]

/-- The mixed linear pair (1,7) has two linear correction factors. Both
commute with the target root, so they collect directly into angular order. -/
theorem last_linear_conjugate (t u : CoefficientField m) :
    L 1 t * L 0 u * (L 1 t)⁻¹ =
      L 3 (titsEnd m t * u) * L 2 (t * titsEnd m u) * L 0 u := by
  have hcomm :
      (L 1 t)⁻¹ * (L 0 u)⁻¹ * L 1 t * L 0 u =
        L 3 (titsEnd m t * u) * L 2 (t * titsEnd m u) := by
    rw [pair_main, pair_main, pair_main, pair_main]
    apply Subtype.ext
    exact ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.rootWord_second_eighth_commutator m t u
  exact conjugate_from_commutator hcomm
    (AngularLinearCommute.linear_commute_family m t (titsEnd m t * u)).1
    (AngularLinearCommute.linear_commute_family m t (t * titsEnd m u)).2.1
    (AngularLinearCommute.linear_commute_family m (titsEnd m t * u) u).2.2.2.1.symm
    (AngularLinearCommute.linear_commute_family m (t * titsEnd m u) u).2.2.2.2.symm

/-- The native ordered tail for positions 1 and 7. -/
def tail17 (t u : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inl 1)) :=
  (1, (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m t * u)), 1,
    (PositiveTables.rootChartEquiv m (.inl 2) (t * titsEnd m u)), 1,
    (PositiveTables.rootChartEquiv m (.inl 0) u), PUnit.unit)

theorem tail17_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (t u : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k)
      (tail sourceOrder (.inl 1)) (tail17 m t u) =
      f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m t * u)) *
        f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (t * titsEnd m u)) *
        f (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) u) := by
  change f (.inr 3) 1 * (f (.inl 3)
    (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m t * u)) *
    (f (.inr 1) 1 * (f (.inl 2)
      (PositiveTables.rootChartEquiv m (.inl 2) (t * titsEnd m u)) *
      (f (.inr 2) 1 * (f (.inl 0)
        (PositiveTables.rootChartEquiv m (.inl 0) u) * (1)))))) = _
  simp only [map_one, one_mul, mul_one, mul_assoc]

/-- Uniqueness identifies the mixed pair's ordered coefficients. -/
theorem table17 (hj : (.inl 0 : PositiveTables.Root) ∈ tail sourceOrder (.inl 1))
    (t u : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inl 1) (.inl 0) hj
      (PositiveTables.rootChartEquiv m (.inl 1) t)
      (PositiveTables.rootChartEquiv m (.inl 0) u) = tail17 m t u := by
  apply AngularPresentation.conjugate_unique
  rw [tail17_word]
  exact last_linear_conjugate m t u

end ReeF4.RootPresentationRecognition.AngularNextTransforms
