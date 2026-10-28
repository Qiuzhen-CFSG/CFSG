module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SignedCharts
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers.Roots

/-!
# Five explicit angular coefficient vectors for the full Ree positive group

The checked split-root commutators determine the action on the perpendicular
and next linear roots. Reflection transports give all four short mixed cases.
The central-curve identity supplies the second Suzuki parameter in the next
linear case, including the nonzero central term at field two. Whole-root
factorization reduces these calculations to the existing matrix identities.

Uniqueness of native angular coordinates then identifies five literal entries
of `AngularPresentation.table`; their word lemmas apply in any realization.
No source comparison or global positive-equation premise is used.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
Fong--Seitz II, Section 10, (10.11)(i), (10.13)(i), (10.15).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularCoefficients
open CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations
open Parabolics.RadicalCoordinates.FixedCoordinates
open SignedGeometry
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

private theorem main_central2 (i : Fin 8) (hi : i ≠ 7) (a b : CoefficientField m) :
    Commute (mainElement m i a) (centralElement m 2 b) :=
  Subtype.ext (ReplacementCentralizerRoots.main_central_2 m i hi a b).eq

private theorem main_central4 (i : Fin 8) (a b : CoefficientField m) :
    Commute (mainElement m i a) (centralElement m 4 b) :=
  Subtype.ext (ReplacementCentralizerRoots.main_central_4 m i a b).eq

private theorem central2_central4 (a b : CoefficientField m) :
    Commute (centralElement m 2 a) (centralElement m 4 b) :=
  Subtype.ext (ReplacementCentralizerRoots.central_commute m a b).eq

private theorem central_inv (i : Fin 8) (hi : i.val % 2 = 0) (a : CoefficientField m) :
    (centralElement m i a)⁻¹ = centralElement m i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←centralElement_add m i hi, CharTwo.add_self_eq_zero,centralElement_zero]

private theorem linear_inv (i : Fin 8) (hi : i.val % 2 ≠ 0) (a : CoefficientField m) :
    (mainElement m i a)⁻¹ = mainElement m i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←mainElement_add m i hi, CharTwo.add_self_eq_zero,mainElement_zero]

private theorem conj_inv_of_right {G : Type*} [Group G] {a b z : G}
    (h : a⁻¹*b⁻¹*a*b = z) (hz : z⁻¹ = z) : a⁻¹*b*a = b*z := by
  calc
    _ = b*(a⁻¹*b⁻¹*a*b)⁻¹ := by group
    _ = _ := by rw [h,hz]

private theorem main_short (a y : CoefficientField m) :
    (S 0 a 0)⁻¹ * L 3 y * S 0 a 0 = S 3 0 (a*y) * L 3 y := by
  rw [main_eq,pair_eq,omega_eq]
  change (mainElement m 0 a)⁻¹ * mainElement m 3 y * mainElement m 0 a =
    centralElement m 2 (a*y) * mainElement m 3 y
  have h : (mainElement m 0 a)⁻¹ * (mainElement m 3 y)⁻¹ *
      mainElement m 0 a * mainElement m 3 y = centralElement m 2 (a*y) :=
    Subtype.ext (rootWord_first_fourth_commutator m a y)
  exact (conj_inv_of_right h (central_inv m 2 (by decide) _)).trans
    (main_central2 m 3 (by decide) y _).eq

private theorem central0_linear3 (b y : CoefficientField m) :
    Commute (S 0 0 b) (L 3 y) := by
  have h : Commute (S 3 0 b) (L 2 y) := by
    rw [omega_eq,pair_eq]
    exact (main_central2 m 5 (by decide) y b).symm
  have h₁ := h.map (MulAut.conj (reflection m (NormalizerPresentation.side true))).toMonoidHom
  have h₂ : Commute (S 2 0 b) (L 3 y) := by
    simpa only [MulEquiv.coe_toMonoidHom, next, Matrix.cons_val, Fin.isValue, Matrix.head_cons, quartet_reflect m true 3 (by decide),pair_reflect m true 2 (by decide)] using h₁
  have h₃ := h₂.map (MulAut.conj (reflection m (NormalizerPresentation.side false))).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom, next, Matrix.cons_val, Fin.isValue, Matrix.head_cons, quartet_reflect m false 2 (by decide),pair_reflect m false 3 (by decide)] using h₃

private theorem central0_linear2 (b y : CoefficientField m) :
    (S 0 0 b)⁻¹ * L 2 y * S 0 0 b = S 3 0 (b*y) * L 2 y := by
  have h : S 3 0 b * L 0 y = L 0 y * S 3 0 b * S 1 0 (b*y) := by
    rw [omega_eq,pair_eq,omega_eq]
    exact Subtype.ext (ReplacementCentralizerRoots.central_eighth m b y)
  have h₁ := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true))) h
  simp only [map_mul] at h₁
  have h₂ : S 2 0 b * L 1 y = L 1 y * S 2 0 b * S 1 0 (b*y) := by
    simpa only [MulEquiv.coe_toMonoidHom, next, Matrix.cons_val, Fin.isValue, Matrix.head_cons, quartet_reflect m true 3 (by decide),pair_reflect m true 0 (by decide),
      quartet_reflect m true 1 (by decide)] using h₁
  have h₃ := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) h₂
  simp only [map_mul] at h₃
  have h₄ : S 0 0 b * L 2 y = L 2 y * S 0 0 b * S 3 0 (b*y) := by
    simpa only [MulEquiv.coe_toMonoidHom, next, Matrix.cons_val, Fin.isValue, Matrix.head_cons, quartet_reflect m false 2 (by decide),pair_reflect m false 1 (by decide),
      quartet_reflect m false 1 (by decide)] using h₃
  have hr : (S 0 0 b)⁻¹ * (L 2 y)⁻¹ * S 0 0 b * L 2 y = S 3 0 (b*y) := by
    calc
      _ = (S 0 0 b)⁻¹ * (L 2 y)⁻¹ * (S 0 0 b * L 2 y) := by group
      _ = _ := by rw [h₄]; group
  have hz : (S 3 0 (b*y))⁻¹ = S 3 0 (b*y) := by
    rw [omega_eq]
    exact central_inv m 2 (by decide) _
  have hd : Commute (L 2 y) (S 3 0 (b*y)) := by
    rw [omega_eq,pair_eq]
    exact main_central2 m 5 (by decide) y (b*y)
  exact (conj_inv_of_right hr hz).trans hd.eq

/-- The complete Suzuki root acts on the perpendicular linear root. -/
theorem short_inverse_conjugate (a b y : CoefficientField m) :
    (S 0 a b)⁻¹ * L 3 y * S 0 a b = S 3 0 (a*y) * L 3 y := by
  have hf : S 0 a b = S 0 a 0 * S 0 0 b := by
    rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
    simp only [add_zero,zero_add,mul_zero]
  have hc : Commute (S 0 0 b) (S 3 0 (a*y)) := by
    rw [omega_eq (m := m) 3]
    exact whole_central m 0 2 (a*y)
      (fun t => ReplacementCentralizerRoots.main_central_2 m 0 (by decide) t (a*y))
      ⟨S 0 0 b, suzuki0_mem m 0 b⟩
  calc
    _ = (S 0 0 b)⁻¹ * ((S 0 a 0)⁻¹ * L 3 y * S 0 a 0) * S 0 0 b := by rw [hf]; group
    _ = S 3 0 (a*y) * ((S 0 0 b)⁻¹ * L 3 y * S 0 0 b) := by
      rw [main_short, ←mul_assoc, hc.inv_left.eq]; group
    _ = _ := by rw [(central0_linear3 m b y).inv_left.eq]; group

private theorem linear3_linear2 (x y : CoefficientField m) : Commute (L 3 x) (L 2 y) := by
  rw [pair_eq,pair_eq]
  apply Subtype.ext
  change Commute (rootWord m 3 x) (rootWord m 5 y)
  open MatrixRelations.LongCommutators in
  have w3 : rootWord m 3 x = X m 10 x * X m 11 (halfFrobenius m x) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  open MatrixRelations.LongCommutators in
  have w5 : rootWord m 5 y = X m 16 y * X m 17 (halfFrobenius m y) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  rw [w3,w5]
  open MatrixRelations.LongCommutators Theory.AlgebraicGroup.StandardRootSystem in
  exact (((xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x y).mul_right
    (xc m 10 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x (halfFrobenius m y))).mul_left
    ((xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) y).mul_right
      (xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) (halfFrobenius m y))))

private theorem main_next (a y : CoefficientField m) :
    (S 0 a 0)⁻¹ * L 2 y * S 0 a 0 = L 3 (titsEnd m a*y) * S 1 0 (a*titsEnd m y) * L 2 y := by
  have h : (mainElement m 0 a)⁻¹ * (mainElement m 5 y)⁻¹ *
      mainElement m 0 a * mainElement m 5 y =
      mainElement m 3 (titsEnd m a*y) * centralElement m 4 (a*titsEnd m y) :=
    Subtype.ext (rootWord_first_sixth_commutator m a y)
  have hz : (mainElement m 3 (titsEnd m a*y) * centralElement m 4 (a*titsEnd m y))⁻¹ =
      mainElement m 3 (titsEnd m a*y) * centralElement m 4 (a*titsEnd m y) := by
    rw [mul_inv_rev,central_inv m 4 (by decide),linear_inv m 3 (by decide)]
    exact (main_central4 m 3 _ _).symm.eq
  have hh := conj_inv_of_right h hz
  have hc := linear3_linear2 m (titsEnd m a*y) y
  rw [pair_eq,pair_eq] at hc
  simp only [Matrix.cons_val,Fin.isValue] at hc
  have hd := main_central4 m 5 y (a*titsEnd m y)
  rw [main_eq,pair_eq,pair_eq,omega_eq]
  simp only [Matrix.cons_val,Fin.isValue]
  calc
    _ = mainElement m 5 y * (mainElement m 3 (titsEnd m a*y) * centralElement m 4 (a*titsEnd m y)) := hh
    _ = _ := by rw [←mul_assoc,hc.symm.eq,mul_assoc,hd.eq,←mul_assoc]

/-- Whole-root inverse conjugation; its middle central coefficient survives at q = 2. -/
theorem next_inverse_conjugate (a b y : CoefficientField m) :
    (S 0 a b)⁻¹ * L 2 y * S 0 a b =
      S 3 0 (b*y) * L 3 (titsEnd m a*y) * S 1 0 (a*titsEnd m y) * L 2 y := by
  have hf : S 0 a b = S 0 a 0 * S 0 0 b := by
    rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
    simp only [add_zero,zero_add,mul_zero]
  have hc : Commute (S 0 0 b) (L 3 (titsEnd m a*y)) := central0_linear3 m b _
  have hd : Commute (S 0 0 b) (S 1 0 (a*titsEnd m y)) := by
    rw [omega_eq (m := m) 1]
    exact whole_central m 0 4 _ (fun t => ReplacementCentralizerRoots.main_central_4 m 0 t _)
      ⟨S 0 0 b,suzuki0_mem m 0 b⟩
  have he : Commute (L 3 (titsEnd m a*y) * S 1 0 (a*titsEnd m y)) (S 3 0 (b*y)) := by
    rw [pair_eq,omega_eq,omega_eq]
    exact (main_central2 m 3 (by decide) _ _).mul_left (central2_central4 m _ _).symm
  calc
    _ = (S 0 0 b)⁻¹ * ((S 0 a 0)⁻¹ * L 2 y * S 0 a 0) * S 0 0 b := by rw [hf]; group
    _ = (L 3 (titsEnd m a*y) * S 1 0 (a*titsEnd m y)) *
        ((S 0 0 b)⁻¹ * L 2 y * S 0 0 b) := by
      rw [main_next]
      simp only [mul_assoc]
      rw [hc.inv_left.left_comm,hd.inv_left.left_comm]
    _ = _ := by rw [central0_linear2,←mul_assoc,he.eq]; simp only [mul_assoc]

private theorem quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
  have he : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [he,CharTwo.add_self_eq_zero,PositiveTables.quartet_zero,Subgroup.coe_one]

/-- The first nontrivial short angular conjugation. -/
theorem short_conjugate (a b y : CoefficientField m) :
    S 0 a b * L 3 y * (S 0 a b)⁻¹ = S 3 0 (a*y) * L 3 y := by
  have h := short_inverse_conjugate m a (b+titsEnd m a*a) y
  rw [←quartet_inv,inv_inv] at h
  exact h

/-- The full angular next-linear coefficients, including both Omega factors. -/
theorem next_conjugate (a b y : CoefficientField m) :
    S 0 a b * L 2 y * (S 0 a b)⁻¹ =
      S 3 0 ((b+titsEnd m a*a)*y) * L 3 (titsEnd m a*y) *
        S 1 0 (a*titsEnd m y) * L 2 y := by
  have h := next_inverse_conjugate m a (b+titsEnd m a*a) y
  rw [←quartet_inv,inv_inv] at h
  exact h

private theorem conjugate_reverse {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) (hz : z⁻¹ = z) : b*a*b⁻¹ = z*a := by
  calc
    _ = z⁻¹ * (z*b) * a * b⁻¹ := by group
    _ = z⁻¹ * (a*b*a⁻¹) * a * b⁻¹ := by rw [h]
    _ = z⁻¹*a := by group
    _ = _ := by rw [hz]

private theorem short_opposite (a b y : CoefficientField m) :
    S 2 a b * L 3 y * (S 2 a b)⁻¹ = S 1 0 (a*y) * L 3 y := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) (short_conjugate m a b y)
  simpa only [map_mul,map_inv,quartet_reflect m false 0 (by decide),
    quartet_reflect m false 3 (by decide),pair_reflect m false 3 (by decide),
    next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h

/-- Ordered angular positions 3 and 6: the reflected short equation. -/
theorem short_reflected_conjugate (a b y : CoefficientField m) :
    L 3 y * S 2 a b * (L 3 y)⁻¹ = S 1 0 (a*y) * S 2 a b := by
  apply conjugate_reverse (short_opposite m a b y)
  simpa only [map_zero,zero_mul,add_zero] using quartet_inv m 1 0 (a*y)

/-- Ordered angular positions 2 and 5: transport by the two supplied reflections. -/
theorem short_shifted_conjugate (a b y : CoefficientField m) :
    S 3 a b * L 2 y * (S 3 a b)⁻¹ = S 1 0 (a*y) * L 2 y := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side true))) (short_opposite m a b y)
  simpa only [map_mul,map_inv,quartet_reflect m true 2 (by decide),
    quartet_reflect m true 1 (by decide),pair_reflect m true 3 (by decide),
    next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h

/-- Ordered angular positions 1 and 4: the remaining short equation. -/
theorem short_perpendicular_conjugate (a b y : CoefficientField m) :
    L 1 y * S 1 a b * (L 1 y)⁻¹ = S 3 0 (a*y) * S 1 a b := by
  have h := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) (short_shifted_conjugate m a b y)
  have hh : S 1 a b * L 1 y * (S 1 a b)⁻¹ = S 3 0 (a*y) * L 1 y := by
    simpa only [map_mul,map_inv,quartet_reflect m false 3 (by decide),
      quartet_reflect m false 1 (by decide),pair_reflect m false 2 (by decide),
      next, Matrix.cons_val,Fin.isValue,Matrix.head_cons] using h
  apply conjugate_reverse hh
  simpa only [map_zero,zero_mul,add_zero] using quartet_inv m 3 0 (a*y)


open Theory.GroupTheory.OrderedRootPresentation

/-- Explicit angular tail for positions 0 and 3. -/
def tail03 (a y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
  (1, (PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)), (PositiveTables.rootChartEquiv m (.inl 3) y), 1, 1, 1, 1, PUnit.unit)

theorem tail03_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail03 m a y) =
      f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)) * f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) y) := by
  change f (.inl 1) 1 * (f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)) * (f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) y) * (f (.inr 1) 1 * (f (.inl 2) 1 * (f (.inr 2) 1 * (f (.inl 0) 1 * (1))))))) = _
  simp only [map_one,one_mul,mul_one]

/-- Uniqueness identifies these explicit coefficients with the literal angular table. -/
theorem table03 (hj : (.inl 3 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 0) (.inl 3) hj
      (PositiveTables.rootChartEquiv m (.inr 0) (a,b)) (PositiveTables.rootChartEquiv m (.inl 3) y) = tail03 m a y := by
  apply AngularPresentation.conjugate_unique
  rw [tail03_word]
  exact short_conjugate m a b y

/-- Explicit angular tail for positions 1 and 4. -/
def tail14 (a b y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inl 1)) :=
  ((PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)), 1, (PositiveTables.rootChartEquiv m (.inr 1) (a,b)), 1, 1, 1, PUnit.unit)

theorem tail14_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail14 m a b y) =
      f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)) * f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (a,b)) := by
  change f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,a*y)) * (f (.inl 3) 1 * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (a,b)) * (f (.inl 2) 1 * (f (.inr 2) 1 * (f (.inl 0) 1 * (1)))))) = _
  simp only [map_one,one_mul,mul_one]

/-- Uniqueness identifies these explicit coefficients with the literal angular table. -/
theorem table14 (hj : (.inr 1 : PositiveTables.Root) ∈ tail sourceOrder (.inl 1))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inl 1) (.inr 1) hj
      (PositiveTables.rootChartEquiv m (.inl 1) y) (PositiveTables.rootChartEquiv m (.inr 1) (a,b)) = tail14 m a b y := by
  apply AngularPresentation.conjugate_unique
  rw [tail14_word]
  exact short_perpendicular_conjugate m a b y

/-- Explicit angular tail for positions 2 and 5. -/
def tail25 (a y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 3)) :=
  (1, (PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)), (PositiveTables.rootChartEquiv m (.inl 2) y), 1, 1, PUnit.unit)

theorem tail25_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail25 m a y) =
      f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)) * f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) y) := by
  change f (.inl 3) 1 * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)) * (f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) y) * (f (.inr 2) 1 * (f (.inl 0) 1 * (1))))) = _
  simp only [map_one,one_mul,mul_one]

/-- Uniqueness identifies these explicit coefficients with the literal angular table. -/
theorem table25 (hj : (.inl 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 3))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 3) (.inl 2) hj
      (PositiveTables.rootChartEquiv m (.inr 3) (a,b)) (PositiveTables.rootChartEquiv m (.inl 2) y) = tail25 m a y := by
  apply AngularPresentation.conjugate_unique
  rw [tail25_word]
  exact short_shifted_conjugate m a b y

/-- Explicit angular tail for positions 3 and 6. -/
def tail36 (a b y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inl 3)) :=
  ((PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)), 1, (PositiveTables.rootChartEquiv m (.inr 2) (a,b)), 1, PUnit.unit)

theorem tail36_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail36 m a b y) =
      f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)) * f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) := by
  change f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*y)) * (f (.inl 2) 1 * (f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) * (f (.inl 0) 1 * (1)))) = _
  simp only [map_one,one_mul,mul_one]

/-- Uniqueness identifies these explicit coefficients with the literal angular table. -/
theorem table36 (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inl 3))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inl 3) (.inr 2) hj
      (PositiveTables.rootChartEquiv m (.inl 3) y) (PositiveTables.rootChartEquiv m (.inr 2) (a,b)) = tail36 m a b y := by
  apply AngularPresentation.conjugate_unique
  rw [tail36_word]
  exact short_reflected_conjugate m a b y

/-- Explicit angular tail for positions 0 and 5. -/
def tail05 (a b y : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
  (1, (PositiveTables.rootChartEquiv m (.inr 3) (0,(b+titsEnd m a*a)*y)), (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)), (PositiveTables.rootChartEquiv m (.inr 1) (0,a*titsEnd m y)), (PositiveTables.rootChartEquiv m (.inl 2) y), 1, 1, PUnit.unit)

theorem tail05_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k) _ (tail05 m a b y) =
      f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,(b+titsEnd m a*a)*y)) * f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)) * f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*titsEnd m y)) * f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) y) := by
  change f (.inl 1) 1 * (f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (0,(b+titsEnd m a*a)*y)) * (f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (titsEnd m a*y)) * (f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,a*titsEnd m y)) * (f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) y) * (f (.inr 2) 1 * (f (.inl 0) 1 * (1))))))) = _
  simp only [map_one,one_mul,mul_one,mul_assoc]

/-- Uniqueness identifies these explicit coefficients with the literal angular table. -/
theorem table05 (hj : (.inl 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a b y : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 0) (.inl 2) hj
      (PositiveTables.rootChartEquiv m (.inr 0) (a,b)) (PositiveTables.rootChartEquiv m (.inl 2) y) = tail05 m a b y := by
  apply AngularPresentation.conjugate_unique
  rw [tail05_word]
  exact next_conjugate m a b y


end ReeF4.RootPresentationRecognition.AngularCoefficients
