module

public import Theory.SpecificGroups.McLaughlin.Multiplier.PrimeSupport
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# The McLaughlin multiplier: reduction to local bounds and a triple cover

The actual Leech triangle-stabilizer model has been fixed in `Basic`.
`PrimeSupport` excludes every kernel prime outside 2, 3 and 5. The remaining
upper-bound inputs are exclusion of 2 and 5 and exclusion of nine-divisibility.
Together they force the kernel order to divide three. An actual finite perfect
central triple cover supplies the lower bound, because the universal lift is
surjective on kernels. Prime order then identifies the kernel as a group.

The conditional assembly below retains all four unproved inputs explicitly;
it does not assert that the McL multiplier has been calculated. It applies to
arbitrary chosen universal coverings, including covering groups in other
universes. The separately stated A.2.19 application needs only the five-primary
exclusion in addition to the already proved prime-support reduction.

Source: Aschbacher–Smith I.1.1–I.1.4(2), printed pp.407–408, and A.2.19,
printed pp.40–41. The final exact calculation remains with
`qt-i01-multiplier-mcl`; `qt-a02-sporadic` owns the final A.2.19 assembly.
For the outstanding local calculations, see R. L. Griess, Jr., *The Schur
multiplier of McLaughlin's simple group*, Arch. Math. 48 (1987), p.31,
doi:10.1007/BF01196350. Its subgroup identifications and local extension
arguments still require proofs for the present model.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier

open Atlas.Sporadic.McLaughlin PerfectCentralCovering Theory.GroupTheory Subgroup

universe u v

/-- The three outstanding primary bounds give divisibility by three for the
whole kernel. No assumption of universality is used. -/
public theorem kernel_card_dvd_three_of_primary_bounds
    {E : Type*} [Group E] [Finite E] (f : Cover E Model)
    (h2 : ¬ 2 ∣ Nat.card f.toMonoidHom.ker)
    (h5 : ¬ 5 ∣ Nat.card f.toMonoidHom.ker)
    (h9 : ¬ 9 ∣ Nat.card f.toMonoidHom.ker) :
    Nat.card f.toMonoidHom.ker ∣ 3 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hk
  by_cases hk0 : k = 0
  · simp [hk0]
  have hpd : p ∣ Nat.card f.toMonoidHom.ker :=
    (show p ∣ p ^ k by simpa using pow_dvd_pow p (by omega : 1 ≤ k)).trans hk
  rcases kernel_prime_support f hp hpd with h | h | h
  · exact (h2 (h ▸ hpd)).elim
  · subst p
    have hk1 : k ≤ 1 := by
      by_contra! h
      exact h9 ((pow_dvd_pow 3 h).trans hk)
    simpa using pow_dvd_pow 3 hk1
  · exact (h5 (h ▸ hpd)).elim

/-- The additional five-primary exclusion supplies the exact source
three-group-center input needed by A.2.19. It remains an explicit premise. -/
public theorem source_center_isThreeGroup_of_not_five_dvd
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (center E)) (hne : center E ≠ ⊥)
    (h5 : ¬ 5 ∣ Nat.card (sourceCover e).toMonoidHom.ker) :
    IsPGroup 3 (center E) := by
  let : Fact p.Prime := ⟨hp⟩
  rcases source_center_prime_eq_three_or_five e hp hp2 hZ hne with h | h
  · exact h ▸ hZ
  · subst p
    have h5' : ¬ 5 ∣ Nat.card (center E) := by rwa [sourceCover_kernel] at h5
    rcases hZ.card_eq_or_dvd with hc | hc
    · exact (hne (Subgroup.card_eq_one.mp hc)).elim
    · exact (h5' hc).elim

/-- An actual triple cover forces three to divide the canonical universal
kernel. The cover is not assumed universal. -/
public theorem three_dvd_universal_kernel_of_triple_cover
    {E : Type*} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    3 ∣ Nat.card (universalProjection Model).ker := by
  let : Group.IsPerfect E := c.isPerfect
  obtain ⟨h, hh, _⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      c.toMonoidHom h (hh ▸ universalProjection_surjective Model) c.ker_le_center
  rw [← hc]
  exact kernel_card_dvd_of_surjective_factor (universalProjection Model)
    c.toMonoidHom h hs hh

/-- Upper/lower-bound assembly for the canonical kernel, retaining every
missing local bound and the actual triple-cover construction. -/
public theorem universal_kernel_equiv_three_of_primary_bounds_and_triple_cover
    (h2 : ¬ 2 ∣ Nat.card (universalProjection Model).ker)
    (h5 : ¬ 5 ∣ Nat.card (universalProjection Model).ker)
    (h9 : ¬ 9 ∣ Nat.card (universalProjection Model).ker)
    {E : Type*} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (PerfectCentralCovering.schurMultiplier Model ≃* Multiplicative (ZMod 3)) := by
  have hcard : Nat.card (universalProjection Model).ker = 3 :=
    Nat.dvd_antisymm
      (kernel_card_dvd_three_of_primary_bounds (universalCover Model) h2 h5 h9)
      (three_dvd_universal_kernel_of_triple_cover c hc)
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩

/-- The same conditional calculation for any chosen universal covering.
The comparison preserves the actual kernel group, not just its cardinality. -/
public theorem kernel_equiv_three_of_primary_bounds_and_triple_cover
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, u, 0} f)
    (h2 : ¬ 2 ∣ Nat.card (universalProjection Model).ker)
    (h5 : ¬ 5 ∣ Nat.card (universalProjection Model).ker)
    (h9 : ¬ 9 ∣ Nat.card (universalProjection Model).ker)
    {E : Type v} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨k⟩ := universal_kernel_equiv_three_of_primary_bounds_and_triple_cover h2 h5 h9 c hc
  exact ⟨(schurMultiplierEquivOfUniversal (MulEquiv.refl Model) f hf).symm.trans k⟩

end Theory.SpecificGroups.McLaughlin.Multiplier
