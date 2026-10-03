module

public import Theory.Frattini.PGroupMap
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.Extraspecial27FixedLayer

/-!
# Frattini displacement on the extraspecial terminal module

A binary action whose second displacements lie in a subgroup has its
Frattini displacement in that subgroup. The displacement modulo the
subgroup is a homomorphism into an elementary abelian function group.

For an automorphism commuting with the actors, pointwise fixation of its
displacement puts every actor displacement in its fixed subgroup. Thus
control on the fixed subgroup reduces the desired Frattini containment
to the preceding general statement.

The principal theorem applies the proved extraspecial order-27 fixed-layer
bound on the order-64 binary module. It retains the literal automorphism
subgroups and all source hypotheses; no normalizer classification or
elementary Frattini quotient is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.47 / PDF p.37,
the large terminal module immediately before (10).
-/

@[expose] public section

open scoped IsMulCommutative

namespace Subgroup

theorem frattini_displacement_le_of_double_displacement
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (actors : Subgroup (MulAut W)) (htwo : IsPGroup 2 actors)
    (layer : Subgroup W)
    (hdouble : ∀ first second : actors, ∀ point : W,
      (point⁻¹ * (second : MulAut W) point)⁻¹ *
        (first : MulAut W) (point⁻¹ * (second : MulAut W) point) ∈ layer) :
    commutatorAction ((frattini actors).map actors.subtype) W ≤ layer := by
  let projection := QuotientGroup.mk' layer
  let displacement : actors →* (W → W ⧸ layer) := {
    toFun := fun actor point => projection (point⁻¹ * (actor : MulAut W) point)
    map_one' := by ext point; simp [projection]
    map_mul' := by
      intro first second
      funext point
      have hfixed := (QuotientGroup.eq_one_iff (N := layer) _).mpr
        (hdouble first second point)
      change projection ((point⁻¹ * (second : MulAut W) point)⁻¹ *
        (first : MulAut W) (point⁻¹ * (second : MulAut W) point)) = 1 at hfixed
      rw [map_mul, map_inv, inv_mul_eq_one] at hfixed
      simp only [map_mul, map_inv] at hfixed
      change projection (point⁻¹ * (first : MulAut W) ((second : MulAut W) point)) =
        projection (point⁻¹ * (first : MulAut W) point) *
          projection (point⁻¹ * (second : MulAut W) point)
      simp only [map_mul, map_inv]
      calc
        (projection point)⁻¹ * projection ((first : MulAut W) ((second : MulAut W) point)) =
            (projection point)⁻¹ * (projection ((first : MulAut W) point) *
              ((projection point)⁻¹ * projection ((second : MulAut W) point))) := by
                rw [hfixed]; simp
        _ = _ := by ac_rfl }
  let _ : IsElementaryAbelian 2 (W → W ⧸ layer) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro value
      funext point
      change value point ^ 2 = 1
      refine QuotientGroup.induction_on (value point) ?_
      intro representative
      change projection representative ^ 2 = 1
      rw [← map_pow]
      have hsquare : representative ^ 2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) representative
      rw [hsquare, map_one] }
  let _ : Fact (IsPGroup 2 actors) := ⟨htwo⟩
  let _ : Fact (IsPGroup 2 (W → W ⧸ layer)) :=
    ⟨IsElementaryAbelian.isPGroup 2 _⟩
  have hmap := frattini_map_le_of_isPGroup (p := 2) displacement
  rw [frattini_eq_bot_of_isElementaryAbelian (R := W → W ⧸ layer) (p := 2)] at hmap
  rw [commutatorAction_eq_closure]
  apply (closure_le (K := layer)).mpr
  rintro _ ⟨actor, point, rfl⟩
  obtain ⟨representative, hrepresentative, heq⟩ := actor.property
  have hzero := hmap (mem_map_of_mem displacement hrepresentative)
  have hpoint := congrFun (mem_bot.mp hzero) point
  change projection (point⁻¹ * (representative : MulAut W) point) = 1 at hpoint
  have hmem := (QuotientGroup.eq_one_iff (N := layer) _).mp hpoint
  change point⁻¹ * (actor : MulAut W) point ∈ layer
  change (representative : MulAut W) = (actor : MulAut W) at heq
  simpa only [heq] using hmem

theorem frattini_displacement_le_of_fixed_layer_action
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (actors : Subgroup (MulAut W)) (htwo : IsPGroup 2 actors)
    (involution : MulAut W)
    (hcommutes : ∀ actor : actors, Commute (actor : MulAut W) involution)
    (hfixes : ∀ actor : actors,
      ∀ point ∈ commutatorAction (zpowers involution) W,
        (actor : MulAut W) point = point)
    (hmiddle : ∀ actor : actors,
      ∀ point ∈ FixedPoints.subgroup (zpowers involution) W,
        point⁻¹ * (actor : MulAut W) point ∈ commutatorAction (zpowers involution) W) :
    commutatorAction ((frattini actors).map actors.subtype) W ≤
      commutatorAction (zpowers involution) W := by
  apply frattini_displacement_le_of_double_displacement actors htwo
  intro first second point
  apply hmiddle first
  intro power
  have hdisplacement : point⁻¹ * involution point ∈
      commutatorAction (zpowers involution) W := by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨involution, mem_zpowers involution⟩, point, rfl⟩
  have hfixed := hfixes second _ hdisplacement
  have hcommute : (second : MulAut W) (involution point) =
      involution ((second : MulAut W) point) :=
    DFunLike.congr_fun (hcommutes second).eq point
  have hpoint : involution (point⁻¹ * (second : MulAut W) point) =
      point⁻¹ * (second : MulAut W) point := by
    rw [map_mul, map_inv]
    rw [map_mul, map_inv, hcommute] at hfixed
    have hexpression : involution ((second : MulAut W) point) =
        (second : MulAut W) point * (point⁻¹ * involution point) :=
      inv_mul_eq_iff_eq_mul.mp hfixed
    rw [hexpression]
    calc
      (involution point)⁻¹ * ((second : MulAut W) point *
          (point⁻¹ * involution point)) =
          ((involution point)⁻¹ * involution point) *
            (point⁻¹ * (second : MulAut W) point) := by ac_rfl
      _ = point⁻¹ * (second : MulAut W) point := by simp
  exact smul_eq_self_of_mem_zpowers power.property hpoint

end Subgroup

/-- The Frattini action on the extraspecial terminal module has displacement
contained in the selected involution's displacement. -/
theorem extraspecial27_frattini_displacement_le
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (oddGroup actors : Subgroup (MulAut W))
    (hodd : IsExtraspecial 3 oddGroup)
    (hoddCard : Nat.card oddGroup = 27) (hspace : Nat.card W = 64)
    (hfull : commutatorAction oddGroup W = ⊤)
    (htwo : IsPGroup 2 actors)
    (hnormalizes : actors ≤ Subgroup.normalizer (oddGroup : Set (MulAut W)))
    (involution : actors)
    (hinvolution : IsInvolution (involution : MulAut W))
    (hgenerates : ⁅oddGroup, Subgroup.zpowers (involution : MulAut W)⁆ = oddGroup)
    (hcenter : ⁅(Subgroup.center oddGroup).map oddGroup.subtype,
      Subgroup.zpowers (involution : MulAut W)⁆ = ⊥)
    (hindex : Nat.card W = 4 * Nat.card
      (FixedPoints.subgroup (Subgroup.zpowers (involution : MulAut W)) W))
    (hcommutes : ∀ actor : actors,
      Commute (actor : MulAut W) (involution : MulAut W))
    (hfixes : ∀ actor : actors,
      ∀ point ∈ commutatorAction (Subgroup.zpowers (involution : MulAut W)) W,
        (actor : MulAut W) point = point) :
    commutatorAction ((frattini actors).map actors.subtype) W ≤
      commutatorAction (Subgroup.zpowers (involution : MulAut W)) W := by
  exact Subgroup.frattini_displacement_le_of_fixed_layer_action
    actors htwo (involution : MulAut W) hcommutes hfixes
    (extraspecial27_fixed_layer_displacement_le oddGroup actors hodd hoddCard hspace
      hfull htwo hnormalizes involution hinvolution hgenerates hcenter hindex hcommutes hfixes)
