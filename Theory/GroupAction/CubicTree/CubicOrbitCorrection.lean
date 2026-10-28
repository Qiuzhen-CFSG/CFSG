module
public import Theory.GroupAction.CubicTree.DistanceTwoGeometry
public import Theory.GroupAction.ThreePointKernelSeparation
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphBalls
public import Theory.GroupTheory.CubicOrbitCorrection

/-!
# Cubic orbit correction on a tree

An automorphism fixing a vertex and an outer point on each of its three
branches fixes the second ball: unique midpoints fix the neighboring
vertices, and two fixed neighbors fix each three-point neighbor set.
An order-three orbit supplies exactly these three branches.

For two involutions inverting the same cubic element, the adjusted product
fixes that orbit. Thus both the adjustment and the product cube fix the
second ball. No identification of this ball fixer with a local center is
used. The literal six-path application is in DGS85 ApartmentExchange.
Source: DGS, Groups and Graphs (1985), (14.17), printed p.223.
-/

public section
open SimpleGraph Theory.GroupTheory.WeakBNPair.RegularTree
namespace Theory.GroupAction.CubicTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

private theorem fixes_middle_and_star (hΓ : Γ.IsAcyclic)
    (hact : ∀ (g : X) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    {m v a : V} (hmv : Γ.Adj m v) (hva : Γ.Adj v a) (hma : m ≠ a)
    (hcard : Nat.card (Γ.neighborSet v) = 3)
    (g : X) (hm : g • m=m) (ha : g • a=a) :
    g • v=v ∧ ∀ w, Γ.Adj v w → g • w=w := by
  have hv : g • v=v := by
    apply DistanceTwoGeometry.midpoint_unique hΓ hma
    · simpa only [hm] using hact g hmv
    · simpa only [ha] using hact g hva
    · exact hmv
    · exact hva
  refine ⟨hv,?_⟩
  apply MulAction.fixes_three_point_set (Γ.neighborSet v) hcard g
  · intro w
    constructor
    · intro hw
      change Γ.Adj v (g • w)
      simpa only [hv] using hact g hw
    · intro hw
      have hvi : g⁻¹ • v=v := by
        calc g⁻¹ • v = g⁻¹ • (g • v) := congrArg (g⁻¹ • ·) hv.symm
             _ = v := inv_smul_smul g v
      change Γ.Adj v w
      simpa only [hvi,inv_smul_smul] using hact g⁻¹ hw
  · exact hmv.symm
  · exact hva
  · exact hma
  · exact hm
  · exact ha

/-- Fixing the center and one outer vertex on each cubic branch fixes the
entire second ball. Acyclicity fixes each branch's middle vertex. -/
theorem fixes_second_ball_of_branch_leaves (hΓ : Γ.IsAcyclic)
    (hact : ∀ (g : X) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (m : V) (g : X) (hm : g • m=m)
    (hleaves : ∀ v, Γ.Adj m v → ∃ a, Γ.Adj v a ∧ m≠a ∧ g • a=a)
    (hcard : ∀ v, Γ.Adj m v → Nat.card (Γ.neighborSet v)=3) :
    g∈graphBallFixer Γ m 2 := by
  rw [mem_graphBallFixer]
  intro w hw
  obtain ⟨p,hp⟩ := exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp : (2 : ℕ∞)≠⊤) hw)
  have hlen : p.length≤2 := ENat.natCast_le_natCast.mp (hp ▸ hw)
  cases p with
  | nil => exact hm
  | @cons _ v _ hmv p =>
    obtain ⟨a,hva,hma,ha⟩ := hleaves v hmv
    obtain ⟨hv,hstar⟩ := fixes_middle_and_star hΓ hact hmv hva hma (hcard v hmv) g hm ha
    have hd : Γ.edist v w≤1 := p.edist_le.trans (by
      apply ENat.natCast_le_natCast.mpr
      simp only [Walk.length_cons] at hlen
      omega)
    rcases edist_le_one_iff_adj_or_eq.mp hd with hadj | rfl
    · exact hstar w hadj
    · exact hv


private theorem cubic_neighbor_cases
    (hact : ∀ (g : X) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    {m v : V} (hmv : Γ.Adj m v) (hcard : Nat.card (Γ.neighborSet m) = 3)
    (d : X) (hd : d ^ 3 = 1) (hdm : d • m = m) (hdv : d • v ≠ v) :
    ∀ w, Γ.Adj m w → w = v ∨ w = d • v ∨ w = d⁻¹ • v := by
  have hdi : d⁻¹ • m = m := by
    calc d⁻¹ • m = d⁻¹ • (d • m) := congrArg (d⁻¹ • ·) hdm.symm
         _ = m := inv_smul_smul d m
  have h2 : d*d = d⁻¹ := by
    apply mul_right_cancel (b := d)
    simpa only [pow_succ, pow_zero, one_mul, inv_mul_cancel] using hd
  have hvdi : v ≠ d⁻¹ • v := by
    intro he
    have he' := congrArg (d • ·) he
    exact hdv (he'.trans (smul_inv_smul d v))
  have hddi : d • v ≠ d⁻¹ • v := by
    intro he
    have he' := congrArg (d • ·) he
    have hfix : d⁻¹ • v = v := by simpa only [←mul_smul,h2,mul_inv_cancel,one_smul] using he'
    exact hvdi hfix.symm
  let f : Fin 3 → Γ.neighborSet m := ![
    ⟨v,hmv⟩,
    ⟨d • v, by
      change Γ.Adj m (d • v)
      simpa only [hdm] using hact d hmv⟩,
    ⟨d⁻¹ • v, by
      change Γ.Adj m (d⁻¹ • v)
      simpa only [hdi] using hact d⁻¹ hmv⟩]
  have hf : Function.Injective f := by
    intro a b he
    have he' := congrArg Subtype.val he
    fin_cases a <;> fin_cases b <;> simp [f] at he' ⊢
    all_goals first | exact (hdv he'.symm).elim | exact (hdv he').elim |
      exact (hvdi he').elim | exact (hvdi he'.symm).elim |
      exact (hddi he').elim | exact (hddi he'.symm).elim
  let : Finite (Γ.neighborSet m) := Nat.finite_of_card_ne_zero (hcard ▸ by decide)
  have hs := (hf.bijective_of_nat_card_le (by simp [hcard])).2
  intro w hw
  obtain ⟨j,hj⟩ := hs ⟨w,hw⟩
  have he := congrArg Subtype.val hj
  fin_cases j
  · exact Or.inl he.symm
  · exact Or.inr (Or.inl he.symm)
  · exact Or.inr (Or.inr he.symm)

/-- A cubic orbit with one vertex beyond each branch determines the second
ball pointwise. The branch coverage follows from degree three and movement. -/
theorem fixes_second_ball_of_cubic_orbit (hΓ : Γ.IsAcyclic)
    (hact : ∀ (g : X) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    {m v a : V} (hmv : Γ.Adj m v) (hva : Γ.Adj v a) (hma : m ≠ a)
    (hcard : Nat.card (Γ.neighborSet m) = 3)
    (hbranch : ∀ w, Γ.Adj m w → Nat.card (Γ.neighborSet w) = 3)
    (d : X) (hd : d^3=1) (hdm : d • m=m) (hdv : d • v≠v)
    (g : X) (hgm : g • m=m) (ha : g • a=a)
    (hda : g • (d • a)=d • a) (hdia : g • (d⁻¹ • a)=d⁻¹ • a) :
    g ∈ graphBallFixer Γ m 2 := by
  apply fixes_second_ball_of_branch_leaves hΓ hact m g hgm _ hbranch
  intro w hw
  rcases cubic_neighbor_cases hact hmv hcard d hd hdm hdv w hw with rfl | rfl | rfl
  · exact ⟨a,hva,hma,ha⟩
  · refine ⟨d • a,hact d hva,?_,hda⟩
    intro he
    exact hma (MulAction.injective d (hdm.trans he))
  · refine ⟨d⁻¹ • a,hact d⁻¹ hva,?_,hdia⟩
    intro he
    have hdi : d⁻¹ • m=m := by
      calc d⁻¹ • m = d⁻¹ • (d • m) := congrArg (d⁻¹ • ·) hdm.symm
           _ = m := inv_smul_smul d m
    exact hma (MulAction.injective d⁻¹ (hdi.trans he))

/-- The exact adjustment and product cube fix the second ball and commute
with the cubic element. The centralizer condition is retained for local
structure arguments, without identifying the full second kernel. -/
theorem inverted_cubic_product_mem_second_ball (hΓ : Γ.IsAcyclic)
    (hact : ∀ (g : X) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    {m v a : V} (hmv : Γ.Adj m v) (hva : Γ.Adj v a) (hma : m ≠ a)
    (hcard : Nat.card (Γ.neighborSet m) = 3)
    (hbranch : ∀ w, Γ.Adj m w → Nat.card (Γ.neighborSet w) = 3)
    (r t d : X) (hd : d^3=1) (hr2 : r*r=1) (ht2 : t*t=1)
    (hrd : r*d*r⁻¹=d⁻¹) (htd : t*d*t⁻¹=d⁻¹)
    (hdm : d • m=m) (hdv : d • v≠v) (hrm : r • m=m) (htm : t • m=m)
    (hr : r • a=a) (ht : t • (d⁻¹ • a)=d⁻¹ • a) :
    Commute (r*t*d) d ∧ r*t*d ∈ graphBallFixer Γ m 2 ∧
      (r*t)^3 ∈ graphBallFixer Γ m 2 := by
  obtain ⟨hc,h₀,h₁,h₂⟩ := Theory.GroupTheory.inverted_cubic_orbit_product_fixes
    r t d a hd hr2 ht2 hrd htd hr ht
  have hg := fixes_second_ball_of_cubic_orbit hΓ hact hmv hva hma hcard hbranch
    d hd hdm hdv (r*t*d) (by simp only [mul_smul,hdm,htm,hrm]) h₀ h₁ h₂
  have he : (r*t*d)^3=(r*t)^3 := by rw [hc.mul_pow,hd,mul_one]
  exact ⟨hc.mul_left (Commute.refl d), hg,
    he ▸ (graphBallFixer Γ m 2).pow_mem hg 3⟩

end Theory.GroupAction.CubicTree
