module

public import Theory.AtlasPort.Janko2.Sporadic.Janko2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.GroupTheory.CoveringKernelTwo

/-!
# The perfect icosian double cover of J₂

The actual quaternionic lattice group maps onto J₂ with kernel its two
central signs. A checked generator has square equal to the negative sign.
Since the quotient is perfect, the square obstruction makes the linear
group perfect as well. This gives a genuine finite quasisimple double cover,
and a lower bound of two on every universal covering kernel.

The permutation carrier used by the classification receives the same cover
through the proved permutation–icosian equivalence. The exact multiplier
calculation still needs an upper bound; the final two theorems state that
remaining premise explicitly. No universality of the linear cover is assumed.

Source: Aschbacher–Smith, I.1.1 and I.1.3(1), printed p.407. The imported
icosian construction is Gerald Höhn's ATLAS work, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, with attribution and license in
its source modules and LICENSES/ATLAS.txt. The square identity is proved in
`IcosianComparison.Generators.Relations` using the actual quaternion matrices.
-/

@[expose] public section

namespace Theory.SpecificGroups.J2HSMultipliers.J2
open Theory.GroupTheory PerfectCentralCovering Atlas.Conway
open Sporadic.LeechRelated.J2.IcosianComparison
universe u

/-- The actual full Hermitian icosian lattice group. -/
abbrev DoubleCover := Atlas.Sporadic.Janko2.LinearCover

/-- Its literal projection onto the projective icosian model. -/
abbrev projection := Atlas.Sporadic.Janko2.projection

/-- The actual kernel, not merely an equal-order model. -/
theorem projection_kernel : projection.ker = icosianCentralSigns :=
  QuotientGroup.ker_mk' _

theorem projection_kernel_eq_center : projection.ker = Subgroup.center DoubleCover := by
  rw [projection_kernel, Atlas.Sporadic.Janko2.center]

/-- The checked square forces the double extension to be perfect. -/
instance doubleCover_perfect : Group.IsPerfect DoubleCover := by
  let := Atlas.Sporadic.Janko2.perfect
  apply isPerfect_of_central_binary_kernel_of_square projection
    Atlas.Sporadic.Janko2.projection_surjective projection_kernel_eq_center.le
    icosianCentralSign (by simpa only [pow_two] using icosianCentralSign_square)
    (fun k hk => (icosianCentralSigns_mem k).mp (projection_kernel ▸ hk))
    Generators.xLift Generators.xLift_square

instance icosian_isQuasisimple : IsQuasisimple Atlas.Sporadic.Janko2.Model where
  toIsPerfect := Atlas.Sporadic.Janko2.perfect
  simple := by
    let := Atlas.Sporadic.Janko2.isSimpleGroup
    have hz : Subgroup.center Atlas.Sporadic.Janko2.Model = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun h => Atlas.Sporadic.Janko2.nonabelian (Subgroup.center_eq_top_iff.mp h))
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

instance doubleCover_isQuasisimple : IsQuasisimple DoubleCover where
  simple := by
    let := Atlas.Sporadic.Janko2.isSimpleGroup
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.Sporadic.Janko2.center).isSimpleGroup

/-- The actual perfect central covering of the icosian quotient. -/
def icosianCover : Covering DoubleCover Atlas.Sporadic.Janko2.Model where
  toMonoidHom := projection
  surjective := Atlas.Sporadic.Janko2.projection_surjective

theorem kernel_card : Nat.card projection.ker = 2 := by
  rw [projection_kernel, icosianCentralSigns_card]

/-- The group structure of the concrete double-cover kernel. -/
noncomputable def kernelEquivTwo : projection.ker ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq kernel_card (by simp)

instance permutation_isQuasisimple : IsQuasisimple Sporadic.LeechRelated.J2.Carrier where
  toIsPerfect := by
    let := Atlas.Sporadic.Janko2.perfect
    exact Group.IsPerfect.ofSurjective (f := comparison.symm.toMonoidHom)
      comparison.symm.surjective
  simple := by
    let : IsSimpleGroup Sporadic.LeechRelated.J2.Carrier := by
      let := Atlas.Sporadic.Janko2.isSimpleGroup
      exact comparison.isSimpleGroup
    have hn : ¬ IsMulCommutative Sporadic.LeechRelated.J2.Carrier := by
      intro h
      apply Atlas.Sporadic.Janko2.nonabelian
      apply isMulCommutative_iff.mpr
      intro a b
      obtain ⟨a, rfl⟩ := comparison.surjective a
      obtain ⟨b, rfl⟩ := comparison.surjective b
      rw [← map_mul, ← map_mul, (isMulCommutative_iff.mp h a b)]
    have hz : Subgroup.center Sporadic.LeechRelated.J2.Carrier = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun h => hn (Subgroup.center_eq_top_iff.mp h))
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- Compose the literal icosian quotient with the established model comparison. -/
noncomputable def permutationCover : Covering DoubleCover Sporadic.LeechRelated.J2.Carrier :=
  (Covering.ofMulEquiv comparison.symm).comp icosianCover

@[simp] theorem permutationCover_apply (x : DoubleCover) :
    permutationCover x = comparison.symm (projection x) := rfl

theorem permutationCover_kernel : permutationCover.toMonoidHom.ker = projection.ker := by
  change (comparison.symm.toMonoidHom.comp projection).ker = _
  exact MonoidHom.ker_comp_of_injective _ _ comparison.symm.injective

/-- The source carrier receives a perfect double cover with this exact kernel. -/
noncomputable def permutationKernelEquivTwo :
    permutationCover.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr permutationCover_kernel).trans kernelEquivTwo

/-- Every chosen universal cover of the icosian model maps onto its concrete double cover. -/
theorem two_dvd_universal_kernel
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Atlas.Sporadic.Janko2.Model)
    (hf : Covering.IsUniversal.{0,u,0} f) : 2 ∣ Nat.card f.toMonoidHom.ker := by
  have h := kernel_card_dvd_of_surjective_factor f.toMonoidHom icosianCover.toMonoidHom
    (hf.lift icosianCover).toMonoidHom (hf.lift icosianCover).surjective
    (congrArg Covering.toMonoidHom (hf.lift_fac icosianCover))
  rwa [show Nat.card icosianCover.toMonoidHom.ker = 2 from kernel_card] at h

/-- The same lower bound for the actual permutation carrier used in the source branches. -/
theorem two_dvd_permutation_universal_kernel
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Sporadic.LeechRelated.J2.Carrier)
    (hf : Covering.IsUniversal.{0,u,0} f) : 2 ∣ Nat.card f.toMonoidHom.ker := by
  have h := kernel_card_dvd_of_surjective_factor f.toMonoidHom permutationCover.toMonoidHom
    (hf.lift permutationCover).toMonoidHom (hf.lift permutationCover).surjective
    (congrArg Covering.toMonoidHom (hf.lift_fac permutationCover))
  rwa [permutationCover_kernel, kernel_card] at h

/-- Full kernel recognition once the independent upper bound is supplied. -/
theorem kernel_equiv_two_of_bound
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Atlas.Sporadic.Janko2.Model)
    (hf : Covering.IsUniversal.{0,u,0} f)
    (hbound : Nat.card (universalProjection Atlas.Sporadic.Janko2.Model).ker ≤ 2) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let c := universalQuasisimpleCover Atlas.Sporadic.Janko2.Model
  have hc : Covering.IsUniversal.{0,0,u} c :=
    universalQuasisimpleCover_isUniversal _
  have hdvd := kernel_card_dvd_of_surjective_factor c.toMonoidHom f.toMonoidHom
    (hc.lift f).toMonoidHom (hc.lift f).surjective
    (congrArg Covering.toMonoidHom (hc.lift_fac f))
  have hle : Nat.card f.toMonoidHom.ker ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hbound
  have hlo : 2 ≤ Nat.card f.toMonoidHom.ker :=
    Nat.le_of_dvd Nat.card_pos (two_dvd_universal_kernel f hf)
  exact ⟨mulEquivOfPrimeCardEq (le_antisymm hle hlo) (by simp)⟩

/-- Literal permutation-model application of the upper/lower-bound argument. -/
theorem permutation_kernel_equiv_two_of_bound
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Sporadic.LeechRelated.J2.Carrier)
    (hf : Covering.IsUniversal.{0,u,0} f)
    (hbound : Nat.card (universalProjection Sporadic.LeechRelated.J2.Carrier).ker ≤ 2) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let c := universalQuasisimpleCover Sporadic.LeechRelated.J2.Carrier
  have hc : Covering.IsUniversal.{0,0,u} c :=
    universalQuasisimpleCover_isUniversal _
  have hdvd := kernel_card_dvd_of_surjective_factor c.toMonoidHom f.toMonoidHom
    (hc.lift f).toMonoidHom (hc.lift f).surjective
    (congrArg Covering.toMonoidHom (hc.lift_fac f))
  have hle : Nat.card f.toMonoidHom.ker ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hbound
  have hlo : 2 ≤ Nat.card f.toMonoidHom.ker :=
    Nat.le_of_dvd Nat.card_pos (two_dvd_permutation_universal_kernel f hf)
  exact ⟨mulEquivOfPrimeCardEq (le_antisymm hle hlo) (by simp)⟩

end Theory.SpecificGroups.J2HSMultipliers.J2
