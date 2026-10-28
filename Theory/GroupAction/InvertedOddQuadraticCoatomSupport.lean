module
public import Theory.GroupAction.InvertedOddFixedSubgroup
public import Theory.GroupAction.NormalizingActor

/-!
# A commuting quadratic actor fixes inverted odd support

Let an odd finite subgroup R act on an abelian group W and be inverted by t.
If b commutes with R and t fixes every b-displacement, then b fixes the full
R-displacement subgroup pointwise. There is no faithfulness, involution,
finite-module, or elementary-module premise.

The b-displacement is R-invariant because b commutes with R. The inverted-odd
fixed-subgroup theorem makes R fix it. For commuting actions the resulting
double-displacement identity is symmetric, so b fixes each R-displacement
generator; closure induction gives the whole support.

This is the coatom support calculation used in Stellmacher (10.1), printed
p.63. The theorem is source-neutral and keeps the supplied action instance.
-/

universe u

public theorem inverted_odd_quadratic_centralizer_fixes_support
    {X W : Type u} [Group X] [CommGroup W] [MulDistribMulAction X W]
    (R : Subgroup X) [Finite R] (hodd : Odd (Nat.card R))
    (inverter actor : X)
    (hinverts : ∀ r ∈ R, inverter * r * inverter⁻¹ = r⁻¹)
    (hcommutes : ∀ r ∈ R, Commute actor r)
    (hfixed : ∀ point ∈ commutatorAction (Subgroup.zpowers actor) W,
      inverter • point = point) :
    ∀ point ∈ commutatorAction R W, actor • point = point := by
  let N := commutatorAction (Subgroup.zpowers actor) W
  have hnormal : R ≤ Subgroup.normalizer (Subgroup.zpowers actor : Set X) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro r hr
    apply Subgroup.mem_centralizer_iff.mpr
    intro power hpower
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpower
    exact ((hcommutes r hr).zpow_left n).eq
  have hstable := commutatorAction_isInvariant_of_normalizing_actor
    (V := W) R (Subgroup.zpowers actor) hnormal
  have hRfixed : ∀ r ∈ R, ∀ point ∈ N, r • point = point :=
    inverted_odd_fixes_invariant_subgroup R hodd inverter hinverts N
      (fun r hr point hp => (hstable.invariant ⟨r, hr⟩ point).mp hp) hfixed
  have hgenerator (r : R) (point : W) :
      actor • (point⁻¹ * ((r : X) • point)) = point⁻¹ * ((r : X) • point) := by
    have hdelta : point⁻¹ * actor • point ∈ N := by
      change point⁻¹ * actor • point ∈ commutatorAction (Subgroup.zpowers actor) W
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨actor, Subgroup.mem_zpowers _⟩, point, rfl⟩
    have hh := hRfixed r r.property _ hdelta
    have hswap : (r : X) • (actor • point) = actor • ((r : X) • point) := by
      rw [← mul_smul, (hcommutes r r.property).eq.symm, mul_smul]
    rw [smul_mul', smul_inv', hswap] at hh
    rw [smul_mul', smul_inv']
    have heq : actor • ((r : X) • point) =
        ((r : X) • point) * (point⁻¹ * actor • point) := by
      exact (inv_mul_eq_iff_eq_mul).mp hh
    rw [heq]
    calc
      (actor • point)⁻¹ * (((r : X) • point) * (point⁻¹ * actor • point)) =
          (point⁻¹ * ((r : X) • point)) * ((actor • point)⁻¹ * actor • point) := by ac_rfl
      _ = _ := by simp
  intro point hpoint
  rw [commutatorAction_eq_closure] at hpoint
  refine Subgroup.closure_induction (p := fun point _ => actor • point = point)
    ?_ ?_ ?_ ?_ hpoint
  · rintro point ⟨r, vector, rfl⟩
    exact hgenerator r vector
  · simp
  · intro left right _ _ hleft hright
    simp only [smul_mul', hleft, hright]
  · intro point _ hpoint
    simp only [smul_inv', hpoint]
