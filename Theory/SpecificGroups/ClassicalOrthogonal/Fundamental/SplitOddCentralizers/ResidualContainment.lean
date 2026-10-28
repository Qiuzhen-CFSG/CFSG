module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.Marked
public import Theory.SpecificGroups.SL2.PrimeToResidual

/-!
# Elementary block images lie in the prime-to-p residual

The Siegel addition law shows that every generator is killed by the field
characteristic. Closure induction therefore puts every image of the actual
elementary group in the prime-to-p residual of its target. The existing SL₂
transvection argument gives the same conclusion for the right determinant
factor. Applying both statements inside the literal centralizer puts the
whole right block image in its nested residual, without perfectness or an
exception at F₃. Isometric transport also proves elementary normality.

Source: the orthogonal rank obstruction in Aschbacher–Smith A.2.17, printed
p.39. This proves the containment needed by that obstruction; equality still
requires the full centralizer and its prime-to-p quotient calculation.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Theory.AlgebraicGroup
universe u
variable {F V W : Type u} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A Siegel generator is killed by the field characteristic. -/
theorem siegelElement_pow_char (p : ℕ) [CharP F p] (Q : QuadraticForm F V)
    (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ^ p = 1 := by
  have hpv (n : ℕ) : Q.polarBilin u (n • v) = 0 := by rw [map_nsmul, huv, nsmul_zero]
  have hpow (n : ℕ) : siegelElement Q u v hu huv ^ n =
      siegelElement Q u (n • v) hu (hpv n) := by
    induction n with
    | zero =>
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change x = Quadratic.siegel Q u (0 • v) x
      simp
    | succ n ih =>
      rw [pow_succ, ih]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Quadratic.siegel Q u (n • v) (Quadratic.siegel Q u v x) =
        Quadratic.siegel Q u ((n + 1) • v) x
      rw [Quadratic.siegel_add Q u (n • v) v x hu (hpv n) huv, succ_nsmul]
  rw [hpow]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Quadratic.siegel Q u (p • v) x = x
  have hv : p • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]
  rw [hv, Quadratic.siegel_zero]

/-- Every image of the elementary group lies in the prime-to-p residual.
This uses its actual Siegel generators, including in characteristic three. -/
theorem elementary_map_mem_primeToResidual (p : ℕ) [CharP F p] (Q : QuadraticForm F V)
    {G : Type*} [Group G] (f : elementarySubgroup Q →* G) (g : elementarySubgroup Q) :
    f g ∈ Subgroup.primeToResidual p G := by
  have h (x : quadraticIsometrySubgroup Q) (hx : x ∈ elementarySubgroup Q) :
      f ⟨x, hx⟩ ∈ Subgroup.primeToResidual p G := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, v, hu, huv, rfl⟩ := hx
      apply Subgroup.mem_primeToResidual_of_pow (n := 1)
      have hp : (⟨siegelElement Q u v hu huv, siegelElement_mem Q u v hu huv⟩ :
          elementarySubgroup Q) ^ p = 1 := Subtype.ext (siegelElement_pow_char p Q u v hu huv)
      simp only [pow_one, ← map_pow, hp, map_one]
    | one => exact (map_one f).symm ▸ (Subgroup.primeToResidual p G).one_mem
    | mul x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
      rw [map_mul]
      exact (Subgroup.primeToResidual p G).mul_mem ihx ihy
    | inv x hx ih =>
      change f (⟨x, hx⟩⁻¹) ∈ _
      rw [map_inv]
      exact (Subgroup.primeToResidual p G).inv_mem ih
  exact h g.val g.prop

/-- The complete right block image is in the actual nested residual's image.
No perfectness, finite-field order formula, or full centralizer equality is used. -/
theorem rightProjective_range_le_residual (p : ℕ) [CharP F p]
    (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S) :
    (rightProjective Q S e).range ≤
      (Subgroup.primeToResidual p
        (Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S)))).map
          (Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S))).subtype := by
  let C := Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S))
  let f : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q →* C :=
    (rightProjective Q S e).codRestrict C
      (fun g => rightProjective_range_le_centralizer Q S e ⟨g, rfl⟩)
  rintro x ⟨g, rfl⟩
  have h1 := Matrix.SL2.map_mem_primeToResidual p (f.comp (MonoidHom.inl _ _)) g.1
  have h2 := elementary_map_mem_primeToResidual p Q (f.comp (MonoidHom.inr _ _)) g.2
  have hg : f g ∈ Subgroup.primeToResidual p C := by
    have heq : g = (g.1, 1) * (1, g.2) := by simp
    rw [heq, f.map_mul]
    exact (Subgroup.primeToResidual p C).mul_mem h1 h2
  exact ⟨f g, hg, rfl⟩


/-- The actual elementary subgroup is normal in the full quadratic-isometry group. -/
theorem elementary_normal (Q : QuadraticForm F V) : (elementarySubgroup Q).Normal where
  conj_mem x hx g := by
    let e : Q.IsometryEquiv Q :=
      { g.val with map_app' := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop }
    have h := conjugate_mem_elementary e (⟨x, hx⟩ : elementarySubgroup Q)
    have heq : conjugate e x = g * x * g⁻¹ := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rfl
    rwa [heq] at h

end ClassicalOrthogonal.Fundamental.SplitOddBlocks
