module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Levels

/-!
# Uniqueness of the preceding line at level four

A singular vector outside the lower plane whose last coordinate is zero has
nonzero coordinate 5 or 6. Either coordinate gives a pivot in the equations
for a lower-plane vector annihilating it: the solution space has dimension at
most one. Explicit scalar multiples identify the resulting projective points.
Thus two level-three lines through a level-four point contain the same
level-two point, and the two distinct points determine their common line.

This proves the `hpoint_four` premise of `metric_girth_of_predecessors` over
every field. Source context is the split G₂ case of Aschbacher--Smith,
Theorem 0.1.2(1), printed pp.3--4, and Theorem 0.1.1, printed pp.481--482.
The coordinate conventions and singular-point APIs are from Gerald Höhn and
the ATLAS contributors' licensed port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. The coordinate and incidence proofs here are new.
-/

@[expose] public section


open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

/-- Three necessary equations for a lower-plane vector annihilating `x`. -/
private theorem lower_annihilator_coordinates {x a : Carrier F}
    (ha : inLowerPlane a) (hax : mul a x = 0) :
    a 1 * x 6 + a 2 * x 5 = 0 ∧
      a 0 * x 5 + a 1 * x 3 = 0 ∧
      -(a 0 * x 6) + a 2 * x 3 = 0 := by
  obtain ⟨h3,h4,h5,h6,h7⟩ := ha
  have h1 := congrFun hax 1
  have h2 := congrFun hax 2
  have he4 := congrFun hax 4
  simp [mul,h3,h4,h5,h6,h7] at h1 h2 he4
  refine ⟨?_,h1,?_⟩
  · linear_combination -he4
  · linear_combination h2

/-- A nonzero coordinate 5 or 6 makes every lower-plane annihilator a scalar
multiple of any fixed nonzero lower-plane annihilator. -/
private theorem lower_annihilator_eq_smul {x a b : Carrier F}
    (hpair : x 5 ≠ 0 ∨ x 6 ≠ 0) (ha : inLowerPlane a) (hb : inLowerPlane b)
    (ha0 : a ≠ 0) (hax : mul a x = 0) (hbx : mul b x = 0) :
    ∃ t : F, t • a = b := by
  obtain ⟨ha12,ha01,ha02⟩ := lower_annihilator_coordinates ha hax
  obtain ⟨hb12,hb01,hb02⟩ := lower_annihilator_coordinates hb hbx
  obtain ⟨ha3,ha4,ha5,ha6,ha7⟩ := ha
  obtain ⟨hb3,hb4,hb5,hb6,hb7⟩ := hb
  -- Coordinate 1 is the free parameter when `x 5 ≠ 0`; otherwise use coordinate 2.
  rcases hpair with h5 | h6
  · have ha1 : a 1 ≠ 0 := by
      intro hz
      have ha0' : a 0 = 0 := (mul_eq_zero.mp (by simpa [hz] using ha01)).resolve_right h5
      have ha2 : a 2 = 0 := (mul_eq_zero.mp (by simpa [hz] using ha12)).resolve_right h5
      apply ha0
      funext i
      fin_cases i <;> simp [ha0',hz,ha2,ha3,ha4,ha5,ha6,ha7]
    refine ⟨b 1 / a 1, ?_⟩
    have he0 : b 1 * a 0 = b 0 * a 1 := by
      apply (mul_right_cancel₀ h5)
      linear_combination b 1 * ha01 - a 1 * hb01
    have he2 : b 1 * a 2 = b 2 * a 1 := by
      apply (mul_right_cancel₀ h5)
      linear_combination b 1 * ha12 - a 1 * hb12
    funext i
    fin_cases i <;> simp [ha3,ha4,ha5,ha6,ha7,hb3,hb4,hb5,hb6,hb7]
    · apply (div_mul_eq_mul_div ..).trans
      exact (div_eq_iff ha1).mpr he0
    · exact div_mul_cancel₀ (b 1) ha1
    · apply (div_mul_eq_mul_div ..).trans
      exact (div_eq_iff ha1).mpr he2
  · have ha2 : a 2 ≠ 0 := by
      intro hz
      have ha0' : a 0 = 0 :=
        (mul_eq_zero.mp (by simpa [hz] using ha02)).resolve_right h6
      have ha1 : a 1 = 0 := (mul_eq_zero.mp (by simpa [hz] using ha12)).resolve_right h6
      apply ha0
      funext i
      fin_cases i <;> simp [ha0',ha1,hz,ha3,ha4,ha5,ha6,ha7]
    refine ⟨b 2 / a 2, ?_⟩
    have he0 : b 2 * a 0 = b 0 * a 2 := by
      apply (mul_right_cancel₀ h6)
      linear_combination -b 2 * ha02 + a 2 * hb02
    have he1 : b 2 * a 1 = b 1 * a 2 := by
      apply (mul_right_cancel₀ h6)
      linear_combination b 2 * ha12 - a 2 * hb12
    funext i
    fin_cases i <;> simp [ha3,ha4,ha5,ha6,ha7,hb3,hb4,hb5,hb6,hb7]
    · apply (div_mul_eq_mul_div ..).trans
      exact (div_eq_iff ha2).mpr he0
    · apply (div_mul_eq_mul_div ..).trans
      exact (div_eq_iff ha2).mpr he1
    · exact div_mul_cancel₀ (b 2) ha2

/-- A level-four point lies on at most one level-three line. -/
theorem metric_point_level_four_predecessor_unique
    (p : SingularPoints F) (L M : ZeroProductLine F)
    (hp : metricPointLevel p = 4) (hpL : pointOnLine p L) (hpM : pointOnLine p M)
    (hL : metricLineLevel L = 3) (hM : metricLineLevel M = 3) : L = M := by
  obtain ⟨_, hpLower, hp7⟩ := (metricPointLevel_eq_four_iff p).mp hp
  have hpair : p.val.rep 5 ≠ 0 ∨ p.val.rep 6 ≠ 0 := by
    by_cases h5 : p.val.rep 5 = 0
    · right
      intro h6
      obtain ⟨h3,h4⟩ := lower_stratum_diagonal_zero p.val.rep p.property.1 p.property.2
        h5 h6 hp7
      exact hpLower ⟨h3,h4,h5,h6,hp7⟩
    · exact Or.inl h5
  obtain ⟨_,a,haL,ha⟩ := (metricLineLevel_eq_three_iff L).mp hL
  obtain ⟨_,b,hbM,hb⟩ := (metricLineLevel_eq_three_iff M).mp hM
  have haLower := (metricPointLevel_eq_two_iff a).mp ha |>.2
  have hbLower := (metricPointLevel_eq_two_iff b).mp hb |>.2
  have hap : mul a.val.rep p.val.rep = 0 :=
    L.property.2 _ ((pointOnLine_iff a L).mp haL) _ ((pointOnLine_iff p L).mp hpL)
  have hbp : mul b.val.rep p.val.rep = 0 :=
    M.property.2 _ ((pointOnLine_iff b M).mp hbM) _ ((pointOnLine_iff p M).mp hpM)
  obtain ⟨t,ht⟩ := lower_annihilator_eq_smul hpair haLower hbLower a.val.rep_nonzero hap hbp
  have hab : a = b := by
    apply Subtype.ext
    have he := (Projectivization.mk_eq_mk_iff' F _ _ b.val.rep_nonzero
      a.val.rep_nonzero).mpr ⟨t,ht⟩
    simpa only [Projectivization.mk_rep] using he.symm
  have hpa : p ≠ a := by
    intro he
    apply hpLower
    simpa only [he] using haLower
  rw [← hab] at hbM
  exact metric_line_unique hpa hpL haL hpM hbM

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
