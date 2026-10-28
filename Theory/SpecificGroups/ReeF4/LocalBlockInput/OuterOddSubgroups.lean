module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The outer restriction for a supplied Ree fixed group

For `m ≥ 1`, every automorphism of the supplied simple, perfect fixed group is
inner times a power of its canonical Frobenius. Inner automorphisms vanish in
the outer quotient, so that quotient is cyclic of order dividing `2 * m + 1`.
In particular it satisfies `HasCyclicNormalOddQuotient`.

The fixed Bruhat calculation supplies odd index of the positive subgroup,
so Sylow conjugacy first normalizes it. Opposite-pair normalization and
inner–field rigidity then give coverage by inner and field automorphisms.
The final theorems discharge all three premises of the retained conditional
reductions. The only group hypotheses are simplicity and perfectness of the
supplied fixed group; no construction-existence or automorphism-classification
hypothesis is added. The full binary Ree group and the Tits simple carrier
remain separate.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510, and Remark A.2.4,
printed p.33 (`refs/quasithin.pdf`); GLS3, §2.5, especially 2.5.12(b–f).
-/

@[expose] public section
namespace ReeF4.LocalBlockInput
variable {m : ℕ}

/-- The canonical cyclic field subgroup maps to the actual outer quotient. -/
noncomputable def fieldOuterHom (d : LocalBlockInput m) :
    Subgroup.zpowers d.fieldAutomorphism →* MulAut.Outer d.fixedGroup :=
  (QuotientGroup.mk' (MulAut.innerSubgroup d.fixedGroup)).comp
    (Subgroup.zpowers d.fieldAutomorphism).subtype

private theorem inner_field_surjective {G : Type*} [Group G] (φ : MulAut G)
    (hcover : ∀ a : MulAut G, ∃ (g : G) (n : ℤ),
      a = MulAut.conj g * φ ^ n) :
    Function.Surjective ((QuotientGroup.mk' (MulAut.innerSubgroup G)).comp
      (Subgroup.zpowers φ).subtype) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup G) q
  obtain ⟨g, n, rfl⟩ := hcover a
  refine ⟨⟨φ ^ n, Subgroup.zpow_mem_zpowers _ n⟩, ?_⟩
  have hg : QuotientGroup.mk' (MulAut.innerSubgroup G) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  change QuotientGroup.mk' _ (φ ^ n) =
    QuotientGroup.mk' _ (MulAut.conj g * φ ^ n)
  rw [map_mul, hg, one_mul]

/-- Inner–field coverage makes the field subgroup surject onto the outer group. -/
theorem fieldOuterHom_surjective_of_inner_field (d : LocalBlockInput m)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (n : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ n) :
    Function.Surjective d.fieldOuterHom := inner_field_surjective _ hcover

/-- The cyclicity conclusion is conditional on coverage of all automorphisms. -/
theorem outer_isCyclic_of_inner_field (d : LocalBlockInput m)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (n : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ n) :
    IsCyclic (MulAut.Outer d.fixedGroup) :=
  isCyclic_of_surjective d.fieldOuterHom (d.fieldOuterHom_surjective_of_inner_field hcover)

/-- Coverage also bounds the outer order by the odd coefficient-field degree. -/
theorem outer_card_dvd_of_inner_field (d : LocalBlockInput m)
    (hcover : ∀ a : MulAut d.fixedGroup, ∃ (g : d.fixedGroup) (n : ℤ),
      a = MulAut.conj g * d.fieldAutomorphism ^ n) :
    Nat.card (MulAut.Outer d.fixedGroup) ∣ 2 * m + 1 := by
  have h := Subgroup.card_dvd_of_surjective d.fieldOuterHom
    (d.fieldOuterHom_surjective_of_inner_field hcover)
  rw [Nat.card_zpowers] at h
  exact h.trans d.orderOf_fieldAutomorphism_dvd

/-- Combine Sylow normalization, opposite-pair normalization, and pair rigidity.
The latter two premises must be proved for the actual fixed group. -/
theorem inner_field_of_unipotent_pair (d : LocalBlockInput m)
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (hnormalize : ∀ a : MulAut d.fixedGroup,
      (LargeLocalSeeds.standardUnipotent d).map a.toMonoidHom =
        LargeLocalSeeds.standardUnipotent d →
      ∃ g : d.fixedGroup, PreservesUnipotentPair d ((MulAut.conj g)⁻¹ * a))
    (hrigid : ∀ a : MulAut d.fixedGroup, PreservesUnipotentPair d a →
      ∃ (g : d.fixedGroup) (n : ℤ), a = MulAut.conj g * d.fieldAutomorphism ^ n)
    (a : MulAut d.fixedGroup) :
    ∃ (g : d.fixedGroup) (n : ℤ), a = MulAut.conj g * d.fieldAutomorphism ^ n := by
  obtain ⟨g, hg⟩ := d.exists_inner_adjustment_preserving_unipotent_of_odd_index hindex a
  obtain ⟨h, hh⟩ := hnormalize _ hg
  obtain ⟨k, n, hk⟩ := hrigid _ hh
  refine ⟨g * (h * k), n, ?_⟩
  calc
    a = MulAut.conj g * (MulAut.conj h *
        ((MulAut.conj h)⁻¹ * ((MulAut.conj g)⁻¹ * a))) := by
      simp only [mul_inv_cancel_left]
    _ = MulAut.conj (g * (h * k)) * d.fieldAutomorphism ^ n := by
      rw [hk]
      simp only [map_mul, mul_assoc]

/-- Conditional assembly for the odd-subgroup restriction on the outer group.
This does not assert that the three geometric premises have been established. -/
theorem outer_cyclicNormalOddQuotient_of_unipotent_pair (d : LocalBlockInput m)
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (hnormalize : ∀ a : MulAut d.fixedGroup,
      (LargeLocalSeeds.standardUnipotent d).map a.toMonoidHom =
        LargeLocalSeeds.standardUnipotent d →
      ∃ g : d.fixedGroup, PreservesUnipotentPair d ((MulAut.conj g)⁻¹ * a))
    (hrigid : ∀ a : MulAut d.fixedGroup, PreservesUnipotentPair d a →
      ∃ (g : d.fixedGroup) (n : ℤ), a = MulAut.conj g * d.fieldAutomorphism ^ n) :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer d.fixedGroup) := by
  let := d.outer_isCyclic_of_inner_field (d.inner_field_of_unipotent_pair hindex hnormalize hrigid)
  exact Theory.GroupTheory.hasCyclicNormalOddQuotient_of_isCyclic

/-- Every automorphism of the supplied large simple Ree fixed group is inner
times a power of canonical Frobenius. Odd index, pair normalization, and
pair rigidity are all discharged for this same fixed group. -/
theorem inner_field (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (a : MulAut d.fixedGroup) :
    ∃ (g : d.fixedGroup) (n : ℤ), a = MulAut.conj g * d.fieldAutomorphism ^ n := by
  have hindex := LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd d
  exact d.inner_field_of_unipotent_pair hindex
    (exists_inner_adjustment_preserving_pair hm d)
    (PairRigidity.inner_field_of_preservesUnipotentPair hm d hindex) a

/-- The outer automorphism group of the supplied large simple Ree group is cyclic. -/
theorem outer_isCyclic (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup] :
    IsCyclic (MulAut.Outer d.fixedGroup) :=
  d.outer_isCyclic_of_inner_field (inner_field hm d)

/-- Its outer order divides the odd degree of the actual coefficient field. -/
theorem outer_card_dvd (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup] :
    Nat.card (MulAut.Outer d.fixedGroup) ∣ 2 * m + 1 :=
  d.outer_card_dvd_of_inner_field (inner_field hm d)

/-- The outer-group restriction needed in the source's odd-prime inspection.
Simplicity and perfectness can be inherited from the source simple group
through its supplied equivalence; no extra geometric premise remains. -/
theorem outer_cyclicNormalOddQuotient (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup] :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer d.fixedGroup) := by
  let := outer_isCyclic hm d
  exact Theory.GroupTheory.hasCyclicNormalOddQuotient_of_isCyclic

end ReeF4.LocalBlockInput
end
