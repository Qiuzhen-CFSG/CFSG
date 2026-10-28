module
public import Theory.GroupTheory.SpecificGroups.OddDihedralCentralizer

/-!
# Self-normalizing two-subgroups of odd dihedral groups

Every nontrivial two-subgroup of a finite group explicitly isomorphic to a
dihedral group of odd rotation order is its own normalizer.

A two-subgroup's order is a power of two dividing twice the odd rotation
order, so it is at most two. A nontrivial two-subgroup therefore has a unique
nonidentity element. Conjugation by its normalizer fixes that element and
hence centralizes the entire subgroup. The odd-dihedral centralizer theorem
makes this normalizer a two-group; the same order bound then forces equality.
All centralizer and cardinal information is transported along the supplied
group isomorphism.

This elementary dihedral fact supplies the quotient normalizer step in the
edge argument for Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37--38;
source: `refs/latex/stellmacher-n-group.tex`. It has no campaign imports.
-/

private theorem card_two_subgroup_le_two
    {D : Type*} [Group D] [Finite D] (n : ℕ) (hn : Odd n)
    (eD : D ≃* DihedralGroup n) (A : Subgroup D) (hA : IsPGroup 2 A) :
    Nat.card A ≤ 2 := by
  have hdiv : Nat.card A ∣ 2 * n := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr eD.toEquiv]
    exact A.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) n := by
    rw [hk]
    exact hn.coprime_two_left.pow_left k
  exact Nat.le_of_dvd (by decide) (hcop.dvd_of_dvd_mul_right hdiv)

private theorem normalizer_le_centralizer_of_card_two
    {D : Type*} [Group D] (A : Subgroup D) (hA : Nat.card A = 2) :
    Subgroup.normalizer (A : Set D) ≤ Subgroup.centralizer (A : Set D) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : D => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun a : D => a * g) heq'
  simpa [mul_assoc] using h.symm

/-- A nontrivial two-subgroup in an odd-dihedral model is self-normalizing. -/
public theorem odd_dihedral_two_subgroup_normalizer
    {D : Type*} [Group D] [Finite D] (n : ℕ) (hn : Odd n)
    (eD : D ≃* DihedralGroup n) (A : Subgroup D)
    (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set D) = A := by
  have hAc : Nat.card A = 2 := by
    have hbound := card_two_subgroup_le_two n hn eD A hA
    have hpos := A.one_lt_card_iff_ne_bot.mpr hne
    omega
  have hmapne : A.map eD.toMonoidHom ≠ ⊥ := by
    intro hh
    apply hne
    apply Subgroup.map_injective (f := eD.toMonoidHom) eD.injective
    simpa using hh
  have hCmap : (Subgroup.centralizer (A : Set D)).map eD.toMonoidHom ≤
      Subgroup.centralizer (A.map eD.toMonoidHom : Set (DihedralGroup n)) := by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (A : Set D) eD.toMonoidHom
  have hCp : IsPGroup 2 (Subgroup.centralizer (A : Set D)) :=
    ((DihedralGroup.isPGroup_centralizer_of_nontrivial_two_subgroup hn
      (A.map eD.toMonoidHom) (hA.map _) hmapne).to_le hCmap).of_equiv
        ((Subgroup.centralizer (A : Set D)).equivMapOfInjective
          eD.toMonoidHom eD.injective).symm
  have hNp := hCp.to_le (normalizer_le_centralizer_of_card_two A hAc)
  exact Subgroup.eq_of_le_of_card_ge A.le_normalizer (by
    rw [hAc]
    exact card_two_subgroup_le_two n hn eD _ hNp) |>.symm
