module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.Preparation
public import Theory.GroupTheory.CentralCoprimeLiftUnique

/-!
# Restricting the marked octad centralizer to its integral sublattice

The negative eigensublattice of the literal octad sign consists exactly of the
Leech vectors supported on the first Golay basis octad. Its integral centralizer
acts by restrictions of the original lattice isometries, preserving their form.
The action kernel therefore consists of the pointwise fixers of this sublattice.

An order-three lift of a quotient element centralizing the octad sign centralizes
its integral representative: conjugation gives another cubic lift, and cubic
lifts through the central two-group are unique. Consequently every local binary
fixed-free cubic has a lift in this integral centralizer satisfying the
Eisenstein polynomial on the whole Leech lattice.

`ImageFusion` is an unproved classification obligation on the literal restriction
image. Its input retains a polynomial lift on the whole Leech lattice; it does
not replace this by fixed-freeness on just the octad sublattice. Together with
`kernel_isTwoGroup` from the `Kernel` module, it feeds `octadLocalFusion_of_imageFusion`.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 (the octad sublattice and
its pointwise stabilizer), 25.9 and Exercise 9.6, p.141 (the cubic class), and
49.3(2), pp.280–281 (local fusion). None of these source classifications is
asserted by the definitions below.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
namespace OctadRestriction

/-- The integral representative of the published `ambientOctad`. -/
def sign : LeechIsometryGroup := signEmbedding (Multiplicative.ofAdd (golayBasis 0))

/-- The literal centralizer in the full integral Leech isometry group. -/
def centralizer : Subgroup LeechIsometryGroup := Subgroup.centralizer {sign}

theorem mem_centralizer {g : LeechIsometryGroup} : g ∈ centralizer ↔ Commute g sign :=
  Subgroup.mem_centralizer_singleton_iff

/-- The negative eigensublattice of the octad sign, with its inherited integral structure. -/
def lattice : Submodule ℤ leech where
  carrier := {x | sign.val x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change sign.val (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  smul_mem' := by
    intro n x hx
    change sign.val (n • x) = -(n • x)
    rw [map_smul, hx, smul_neg]

theorem mem_lattice_iff_support (x : leech) :
    x ∈ lattice ↔ ∀ i : Omega, (golayBasis 0).val i = 0 → x.val i = 0 := by
  constructor
  · intro hx i hi
    have he := congrArg (fun y : leech => y.val i) hx
    change (if (golayBasis 0).val i = 0 then x.val i else -x.val i) = -x.val i at he
    rw [if_pos hi] at he
    omega
  · intro hx
    apply Subtype.ext
    funext i
    change (if (golayBasis 0).val i = 0 then x.val i else -x.val i) = -x.val i
    by_cases hi : (golayBasis 0).val i = 0
    · simp only [if_pos hi, hx i hi, neg_zero]
    · rw [if_neg hi]

theorem preserves_lattice (g : centralizer) {x : leech} (hx : x ∈ lattice) :
    g.val.val x ∈ lattice := by
  have h := congrArg (fun r : LeechIsometryGroup => r.val x) (mem_centralizer.mp g.prop).eq
  change sign.val (g.val.val x) = -(g.val.val x)
  change sign.val x = -x at hx
  change g.val.val (sign.val x) = sign.val (g.val.val x) at h
  rw [← h, hx, map_neg]

/-- Restriction of actual centralizer elements, not an abstract orthogonal model. -/
def action : centralizer →* (lattice ≃ₗ[ℤ] lattice) where
  toFun g :=
    { toFun := fun x => ⟨g.val.val x.val, preserves_lattice g x.prop⟩
      invFun := fun x => ⟨g⁻¹.val.val x.val, preserves_lattice g⁻¹ x.prop⟩
      left_inv := by intro x; apply Subtype.ext; exact g.val.val.symm_apply_apply x.val
      right_inv := by intro x; apply Subtype.ext; exact g.val.val.apply_symm_apply x.val
      map_add' := by intro x y; apply Subtype.ext; exact map_add g.val.val x.val y.val
      map_smul' := by intro n x; apply Subtype.ext; exact map_smul g.val.val n x.val }
  map_one' := by ext x; rfl
  map_mul' := by intro g h; ext x; rfl

theorem action_apply (g : centralizer) (x : lattice) :
    (action g x).val = g.val.val x.val := rfl

theorem action_preserves_form (g : centralizer) (x y : lattice) :
    integerDot (action g x).val.val (action g y).val.val =
      integerDot x.val.val y.val.val := g.val.prop x.val y.val

theorem mem_action_ker (g : centralizer) :
    g ∈ action.ker ↔ ∀ x : lattice, g.val.val x.val = x.val := by
  constructor
  · intro hg x
    exact congrArg (fun e : lattice ≃ₗ[ℤ] lattice => (e x).val) hg
  · intro hg
    apply LinearEquiv.ext
    intro x
    exact Subtype.ext (hg x)

abbrev Image := action.range

/-- The witness retains the polynomial on the whole integral Leech lattice. -/
def HasPolynomialLift (u : Image) : Prop :=
  ∃ r : centralizer, action r = u.val ∧ orderOf r = 3 ∧
    ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0

/-- A remaining classification obligation on the literal restriction image. -/
def ImageFusion : Prop :=
  ∀ u v : Image, HasPolynomialLift u → HasPolynomialLift v →
    ∃ c : Image, Subgroup.zpowers u.val =
      (Subgroup.zpowers v.val).map (MulAut.conj c.val).toMonoidHom

theorem polynomial_on_lattice {r : centralizer}
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0)
    (x : lattice) : action r (action r x) + action r x + x = 0 := by
  apply Subtype.ext
  exact hr x.val

/-- The original central quotient map restricted to the integral centralizer. -/
def projection : centralizer →* LeechCentralQuotient :=
  leechCentralProjection.comp centralizer.subtype

theorem projection_commutes (g : centralizer) : Commute (projection g) ambientOctad :=
  (mem_centralizer.mp g.prop).map leechCentralProjection

private theorem signs_two : IsPGroup 2 leechCentralProjection.ker := by
  apply IsPGroup.of_card (n := 1)
  rw [leechCentralProjection_kernel, leechCentralSigns_card]
  norm_num

theorem lift_commutes {r : LeechIsometryGroup} (hr : orderOf r = 3)
    (hc : Commute (leechCentralProjection r) ambientOctad) : Commute r sign := by
  have hp : r ^ 3 = 1 := hr ▸ pow_orderOf_eq_one r
  have he : MulAut.conj sign r = r :=
    leechCentralProjection.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
      (by rw [leechCentralProjection_kernel, leechCentralSigns_eq_center]) signs_two
      (by decide : Nat.Coprime 2 3)
      (by
        change leechCentralProjection (sign * r * sign⁻¹) = leechCentralProjection r
        rw [map_mul, map_mul, map_inv]
        change ambientOctad * leechCentralProjection r * ambientOctad⁻¹ = _
        rw [← hc.eq, mul_inv_cancel_right])
      (by rw [← map_pow, hp, map_one]) hp
  have he' : sign * r * sign⁻¹ = r := he
  change r * sign = sign * r
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    (congrArg (· * sign) he').symm

theorem exists_polynomial_lift_in_centralizer {a : LeechCentralQuotient}
    (ha : orderOf a = 3) (hf : CubicFixedFree a) (hc : Commute a ambientOctad) :
    ∃ r : centralizer, projection r = a ∧ orderOf r = 3 ∧
      ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0 := by
  obtain ⟨r, hr, ho, hp⟩ := exists_polynomial_lift ha hf
  let r' : centralizer := ⟨r, mem_centralizer.mpr (lift_commutes ho (hr.symm ▸ hc))⟩
  refine ⟨r', hr, ?_, hp⟩
  exact (Subgroup.orderOf_mk r _).trans ho

end OctadRestriction
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
