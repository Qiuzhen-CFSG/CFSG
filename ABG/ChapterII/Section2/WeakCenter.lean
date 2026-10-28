module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section1.Center

/-!
# Weakly closed central subgroups in Q-groups

Every finite Q-group has a Sylow two-subgroup all of whose central subgroups
are weakly closed in the ambient group. This extracts the clause needed in
ABG Chapter II §3 Proposition 1 from the enlarged definition in §2 Definition 3,
while retaining the original full-Sylow Q alternatives from §1.

The wreathed and overgroup alternatives explicitly include this property.
For the quasi-dihedral alternative, only the entire center is stipulated to
be weakly closed. Its center has order two by §1 Lemma 1(v), so Lagrange's
theorem says every subgroup of it is trivial or is the whole center.

Source: `refs/latex/alperin-brauer-gorenstein-pages/page-011.tex`,
`page-012.tex`, and `page-015.tex` (the two Q-patterns and enlarged definition).
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

private theorem weak_center_of_card_two (S : Subgroup G)
    (hcard : Nat.card (Subgroup.center S) = 2)
    (hweak : BenderSuzuki.External.WeaklyClosedIn S (subgroupCenter S)) :
    HasWeaklyClosedCenterSubgroups S := by
  intro Z hZ
  have hcard' : Nat.card (subgroupCenter S) = 2 := by
    rw [subgroupCenter, Subgroup.card_map_of_injective S.subtype_injective, hcard]
  have hdiv := Subgroup.card_dvd_of_le hZ
  rw [hcard', Nat.dvd_prime Nat.prime_two] at hdiv
  rcases hdiv with hbot | hfull
  · have : Z = ⊥ := (Subgroup.card_eq_one).mp hbot
    subst Z
    refine ⟨bot_le, ?_⟩
    intro g _
    simp [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy]
  · have : Z = subgroupCenter S :=
      Subgroup.eq_of_le_of_card_ge hZ (by omega)
    rwa [this]

/-- The enlarged Q-group definition supplies a Sylow subgroup with every
central subgroup weakly closed. -/
public theorem IsQGroup.exists_hasWeaklyClosedCenterSubgroups (hQ : IsQGroup G) :
    ∃ S : Sylow 2 G, HasWeaklyClosedCenterSubgroups (S : Subgroup G) := by
  rcases hQ with (hquasi | hwreath) | hover
  · obtain ⟨S, T, Q, hframe, hpattern⟩ := hquasi
    exact ⟨S, weak_center_of_card_two (S : Subgroup G) (QuasiDihedral.card_center hframe.1) hpattern.2.1⟩
  · obtain ⟨S, n, U, V, _, hpattern⟩ := hwreath
    exact ⟨S, hpattern.2.1⟩
  · obtain ⟨S, inst, _, R, f, Y, K, _, _, _, _, _, hweak, _⟩ := hover
    exact ⟨R, hweak⟩
end ABG
