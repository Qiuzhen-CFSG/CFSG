module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Metric.Levels

/-!
# Line layers in the intrinsic octonion geometry

Every incident point and line have consecutive algebraic levels, and each line
has at most one point at the preceding level. These are the two line premises
of `metric_girth_of_predecessors`, proved here over every field.

The product coordinates 0 and 7 give vanishing determinants on coordinate pairs
1,2 and 5,6, respectively. Rank-nullity in a two-dimensional line then shows
that a line in the lower plane contains the first point, while a line in its
polar hyperplane contains a lower-plane point. Product coordinates 5 and 6
also force any line through a noninitial lower-plane point to be polar.
Two distinct projective points span their line, so these containment results
give uniqueness in line levels 3 and 5; the remaining level cases are immediate.

The split-octonion coordinates and singular points are from the licensed ATLAS
port (see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`). Source context
is the split G₂ case of Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4,
and Theorem 0.1.1, printed pp.481--482. The results here are intrinsic geometry
lemmas supporting that case, derived from the actual octonion product.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

private theorem coordinate_kernel_nonzero (L : ZeroProductLine F) (i : Fin 8) :
    ∃ x : Carrier F, x ∈ L.val ∧ x ≠ 0 ∧ x i = 0 := by
  let e : L.val →ₗ[F] F := (LinearMap.proj i).comp L.val.subtype
  have hk : LinearMap.ker e ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_self, L.property.1]
    decide)
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x.val, x.property, fun h => hne (Subtype.ext h), hx⟩

private theorem coordinate_pair_kernel (L : ZeroProductLine F) (i j : Fin 8)
    (hdet : ∀ x ∈ L.val, ∀ y ∈ L.val, x i * y j - x j * y i = 0) :
    ∃ x : Carrier F, x ∈ L.val ∧ x ≠ 0 ∧ x i = 0 ∧ x j = 0 := by
  classical
  by_cases hi : ∀ y ∈ L.val, y i = 0
  · obtain ⟨x,hx,hne,hj⟩ := coordinate_kernel_nonzero L j
    exact ⟨x,hx,hne,hi x hx,hj⟩
  · push Not at hi
    obtain ⟨y,hy,hyi⟩ := hi
    obtain ⟨x,hx,hne,hxi⟩ := coordinate_kernel_nonzero L i
    refine ⟨x,hx,hne,hxi,?_⟩
    have hd := hdet y hy x hx
    simp only [hxi, mul_zero, sub_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left hyi

private theorem firstPoint_incident (L : ZeroProductLine F) :
    pointOnLine (firstPoint (K := F)) L ↔ basisVector 0 ∈ L.val := by
  change (Projectivization.mk F (basisVector 0) _).submodule ≤ L.val ↔ _
  rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

private theorem firstPoint_of_lower_coords {p : SingularPoints F}
    (hl : inLowerPlane p.val.rep) (h1 : p.val.rep 1 = 0) (h2 : p.val.rep 2 = 0) :
    p = firstPoint := by
  apply Subtype.ext
  rw [← Projectivization.mk_rep p.val]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨p.val.rep 0, ?_⟩
  obtain ⟨h3,h4,h5,h6,h7⟩ := hl
  ext i
  fin_cases i <;> simp [basisVector,h1,h2,h3,h4,h5,h6,h7]

/-- A line through the first point lies in its simultaneous annihilator. -/
private theorem metric_line_lower_of_first (L : ZeroProductLine F)
    (hL : pointOnLine firstPoint L) {x : Carrier F} (hx : x ∈ L.val) :
    inLowerPlane x := by
  have h0 := (firstPoint_incident L).mp hL
  exact (inLowerPlane_iff_annihilator x).mpr
    ⟨L.property.2 _ h0 _ hx, L.property.2 _ hx _ h0⟩

/-- A two-dimensional zero-product subspace of the lower plane contains the first point. -/
private theorem metric_line_first_of_lower (L : ZeroProductLine F)
    (hL : ∀ x ∈ L.val, inLowerPlane x) : pointOnLine firstPoint L := by
  have hdet : ∀ x ∈ L.val, ∀ y ∈ L.val, x 1 * y 2 - x 2 * y 1 = 0 := by
    intro x hx y hy
    obtain ⟨hx3,_,_,_,_⟩ := hL x hx
    obtain ⟨_,hy4,_,_,_⟩ := hL y hy
    have hc := congrFun (L.property.2 x hx y hy) 0
    simp [mul,hx3,hy4] at hc
    linear_combination -hc
  obtain ⟨x,hx,hne,h1,h2⟩ := coordinate_pair_kernel L 1 2 hdet
  obtain ⟨h3,h4,h5,h6,h7⟩ := hL x hx
  have he : x 0 • basisVector 0 = x := by
    ext i
    fin_cases i <;> simp [basisVector,h1,h2,h3,h4,h5,h6,h7]
  have hn0 : x 0 ≠ 0 := by
    intro h0
    apply hne
    rw [← he,h0,zero_smul]
  apply (firstPoint_incident L).mpr
  exact (L.val.smul_mem_iff hn0).mp (he.symm ▸ hx)

/-- A lower-plane point other than the first forces its incident line to be polar. -/
private theorem metric_line_polar_of_lower {p : SingularPoints F} {L : ZeroProductLine F}
    (hne : p ≠ firstPoint) (hl : inLowerPlane p.val.rep) (hp : pointOnLine p L)
    {x : Carrier F} (hx : x ∈ L.val) : x 7 = 0 := by
  have hp' := (pointOnLine_iff p L).mp hp
  have hc := L.property.2 p.val.rep hp' x hx
  obtain ⟨h3,h4,h5,h6,h7⟩ := hl
  by_cases h1 : p.val.rep 1 = 0
  · have h2 : p.val.rep 2 ≠ 0 := fun h2 =>
      hne (firstPoint_of_lower_coords ⟨h3,h4,h5,h6,h7⟩ h1 h2)
    have h := congrFun hc 6
    simp [mul,h3,h6,h7] at h
    exact h.resolve_left h2
  · have h := congrFun hc 5
    simp [mul,h3,h5,h7] at h
    exact h.resolve_left h1

/-- A zero-product line contained in the polar hyperplane meets the lower plane. -/
private theorem metric_line_has_lower_point_of_polar (L : ZeroProductLine F)
    (hL : ∀ x ∈ L.val, x 7 = 0) :
    ∃ p : SingularPoints F, pointOnLine p L ∧ inLowerPlane p.val.rep := by
  have hdet : ∀ x ∈ L.val, ∀ y ∈ L.val, x 5 * y 6 - x 6 * y 5 = 0 := by
    intro x hx y hy
    simpa [mul,hL x hx,hL y hy] using congrFun (L.property.2 x hx y hy) 7
  obtain ⟨x,hx,hne,h5,h6⟩ := coordinate_pair_kernel L 5 6 hdet
  have hs := metric_line_singular L hx
  have h7 := hL x hx
  obtain ⟨h3,h4⟩ := lower_stratum_diagonal_zero x hs.1 hs.2 h5 h6 h7
  let p := singularPointMk F x hne hs.1 hs.2
  refine ⟨p, ?_, ?_⟩
  · change (Projectivization.mk F x hne).submodule ≤ L.val
    rwa [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
  · change inLowerPlane (Projectivization.mk F x hne).rep
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F x hne
    rw [← ha]
    simp [inLowerPlane,h3,h4,h5,h6,h7]

/-- Distinct lower-plane points on a line force the first point onto that line. -/
private theorem metric_line_first_of_two_lower {p q : SingularPoints F} {L : ZeroProductLine F}
    (hne : p ≠ q) (hp : pointOnLine p L) (hq : pointOnLine q L)
    (hpl : inLowerPlane p.val.rep) (hql : inLowerPlane q.val.rep) :
    pointOnLine firstPoint L := by
  apply metric_line_first_of_lower
  intro x hx
  rw [metric_line_eq_span hne hp hq] at hx
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨hp3,hp4,hp5,hp6,hp7⟩ := hpl
  obtain ⟨hq3,hq4,hq5,hq6,hq7⟩ := hql
  simp [inLowerPlane,hp3,hp4,hp5,hp6,hp7,hq3,hq4,hq5,hq6,hq7]

/-- Distinct polar points on a line force a lower-plane point onto it. -/
private theorem metric_line_lower_of_two_polar {p q : SingularPoints F} {L : ZeroProductLine F}
    (hne : p ≠ q) (hp : pointOnLine p L) (hq : pointOnLine q L)
    (hp7 : p.val.rep 7 = 0) (hq7 : q.val.rep 7 = 0) :
    ∃ r : SingularPoints F, pointOnLine r L ∧ inLowerPlane r.val.rep := by
  apply metric_line_has_lower_point_of_polar
  intro x hx
  rw [metric_line_eq_span hne hp hq] at hx
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [hp7,hq7]

private theorem line_level_five (L : ZeroProductLine F) :
    metricLineLevel L = 5 ↔ ¬ pointOnLine firstPoint L ∧
      ¬ ∃ p : SingularPoints F, pointOnLine p L ∧ metricPointLevel p = 2 := by
  classical
  unfold metricLineLevel
  split_ifs <;> simp_all

/-- Every incidence joins consecutive algebraic levels. -/
theorem metric_line_step (L : ZeroProductLine F) (p : SingularPoints F)
    (hp : pointOnLine p L) :
    metricPointLevel p + 1 = metricLineLevel L ∨
      metricLineLevel L + 1 = metricPointLevel p := by
  classical
  rcases metricLineLevel_cases L with h1 | h3 | h5
  · have hfirst := (metricLineLevel_eq_one_iff L).mp h1
    by_cases he : p = firstPoint
    · subst p
      simp [h1]
    · have hl := metric_line_lower_of_first L hfirst ((pointOnLine_iff p L).mp hp)
      have hp2 := (metricPointLevel_eq_two_iff p).mpr ⟨he,hl⟩
      omega
  · obtain ⟨hfirst,q,hq,hq2⟩ := (metricLineLevel_eq_three_iff L).mp h3
    have hpne : p ≠ firstPoint := fun he => hfirst (he ▸ hp)
    have hql := (metricPointLevel_eq_two_iff q).mp hq2
    have hp7 := metric_line_polar_of_lower hql.1 hql.2 hq
      ((pointOnLine_iff p L).mp hp)
    by_cases hpl : inLowerPlane p.val.rep
    · have hp2 := (metricPointLevel_eq_two_iff p).mpr ⟨hpne,hpl⟩
      omega
    · have hp4 := (metricPointLevel_eq_four_iff p).mpr ⟨hpne,hpl,hp7⟩
      omega
  · obtain ⟨hfirst,hlower⟩ := (line_level_five L).mp h5
    have hpne : p ≠ firstPoint := fun he => hfirst (he ▸ hp)
    have hpl : ¬ inLowerPlane p.val.rep := fun hl =>
      hlower ⟨p,hp,(metricPointLevel_eq_two_iff p).mpr ⟨hpne,hl⟩⟩
    by_cases hp7 : p.val.rep 7 = 0
    · have hp4 := (metricPointLevel_eq_four_iff p).mpr ⟨hpne,hpl,hp7⟩
      omega
    · have hp6 : metricPointLevel p = 6 := by simp [metricPointLevel,hpne,hpl,hp7]
      omega

/-- Every line has at most one incident point at the preceding algebraic level. -/
theorem metric_line_unique_preceding_point (L : ZeroProductLine F)
    (p q : SingularPoints F) (hp : pointOnLine p L) (hq : pointOnLine q L)
    (hpl : metricPointLevel p + 1 = metricLineLevel L)
    (hql : metricPointLevel q + 1 = metricLineLevel L) : p = q := by
  classical
  rcases metricLineLevel_cases L with h1 | h3 | h5
  · have hp0 : metricPointLevel p = 0 := by omega
    have hq0 : metricPointLevel q = 0 := by omega
    exact ((metricPointLevel_eq_zero_iff p).mp hp0).trans
      ((metricPointLevel_eq_zero_iff q).mp hq0).symm
  · obtain ⟨hfirst,_⟩ := (metricLineLevel_eq_three_iff L).mp h3
    have hp2 : metricPointLevel p = 2 := by omega
    have hq2 : metricPointLevel q = 2 := by omega
    by_contra hne
    exact hfirst (metric_line_first_of_two_lower hne hp hq
      ((metricPointLevel_eq_two_iff p).mp hp2).2
      ((metricPointLevel_eq_two_iff q).mp hq2).2)
  · obtain ⟨hfirst,hlower⟩ := (line_level_five L).mp h5
    have hp4 : metricPointLevel p = 4 := by omega
    have hq4 : metricPointLevel q = 4 := by omega
    by_contra hne
    obtain ⟨r,hr,hrl⟩ := metric_line_lower_of_two_polar hne hp hq
      ((metricPointLevel_eq_four_iff p).mp hp4).2.2
      ((metricPointLevel_eq_four_iff q).mp hq4).2.2
    have hrne : r ≠ firstPoint := fun he => hfirst (he ▸ hr)
    exact hlower ⟨r,hr,(metricPointLevel_eq_two_iff r).mpr ⟨hrne,hrl⟩⟩

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
