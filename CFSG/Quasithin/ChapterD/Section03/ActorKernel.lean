module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Proper invariant subgroups of the D.3.1 actor

Every proper subgroup of the source actor `X` that is normal in `X T` lies
in its Frattini subgroup. In the component-orbit case, the component
normal-subgroup dichotomy forces this subgroup to centralize the entire
orbit. The orbit is perfect, so its center lies in its Frattini subgroup.
In the odd-prime case, the literal conjugation action preserves its image
in the Frattini quotient. Irreducibility and Frattini nongeneration force
that image to be trivial.

This is the structural kernel bound in the proof of Aschbacher–Smith,
combined manuscript of 1 March 2004, Lemma D.3.4(2), printed p.194.
No kernel containment or irreducibility conclusion is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative


namespace CFSG.Quasithin.ChapterD.Section03
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_orbit_proper_normal_le_frattini
    {X L A N : Subgroup G} (hL : IsComponent G L)
    (hX : X = componentOrbit L A) (hNX : N ≤ X)
    (hn : X ⊔ A ≤ normalizer (N : Set G)) (hne : N ≠ X) :
    N ≤ (frattini X).map X.subtype := by
  have hLX : L ≤ X := by
    rw [hX]
    exact le_componentOrbit L A
  let : (N.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNX).mpr (le_sup_left.trans hn)
  let : Group.IsPerfect X := by
    rw [hX]
    exact hL.orbit_isPerfect A
  have hc : ⁅L, N⁆ = ⊥ := by
    rcases (hL.subgroupOf hLX).normal_dichotomy (N.subgroupOf X) with hLN | hc
    · have hLN' : L ≤ N := by
        simpa only [map_subgroupOf_eq_of_le hLX, map_subgroupOf_eq_of_le hNX]
          using map_mono (f := X.subtype) hLN
      have hXN : X ≤ N := by
        rw [hX]
        exact iSup_conjugates_le_of_le_normalizer L A N hLN' (le_sup_right.trans hn)
      exact (hne (le_antisymm hNX hXN)).elim
    · simpa only [map_commutator, map_subgroupOf_eq_of_le hLX,
        map_subgroupOf_eq_of_le hNX, Subgroup.map_bot] using congrArg (map X.subtype) hc
  have hXC : X ≤ centralizer (N : Set G) := by
    rw [hX]
    exact iSup_conjugates_le_centralizer L A N (le_sup_right.trans hn) hc
  have hNZ : N.subgroupOf X ≤ center X := by
    intro n hn
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (hXC x.property (n : G) hn).symm
  rw [← map_subgroupOf_eq_of_le hNX]
  exact map_mono (hNZ.trans center_le_frattini_of_isPerfect)

private theorem FrattiniIrreducible.proper_normalized_le_frattini
    {T X N : Subgroup G} {hTX : T ≤ normalizer (X : Set G)}
    (hI : FrattiniIrreducible T X hTX) (hNX : N ≤ X)
    (hn : T ≤ normalizer (N : Set G)) (hne : N ≠ X) :
    N ≤ (frattini X).map X.subtype := by
  let q := QuotientGroup.mk' (frattini X)
  let A := (N.subgroupOf X).map q
  have hinv : ∀ t : T, ∀ a ∈ A, frattiniAction T X hTX t a ∈ A := by
    rintro t a ⟨n, hnN, rfl⟩
    refine ⟨X.normalizerMonoidHom ⟨t, hTX t.property⟩ n, ?_, ?_⟩
    · change (t : G) * (n : G) * (t : G)⁻¹ ∈ N
      exact (mem_normalizer_iff.mp (hn t.property) n).mp hnN
    · change q (X.normalizerMonoidHom ⟨t, hTX t.property⟩ n) =
        quotientAut (frattini X) (X.normalizerMonoidHom (inclusion hTX t)) (q n)
      rw [show inclusion hTX t = ⟨t, hTX t.property⟩ from rfl]
      exact (quotientAut_apply_mk (frattini X)
        (X.normalizerMonoidHom ⟨t, hTX t.property⟩) n).symm
  rcases hI A hinv with hb | ht
  · have hNphi : N.subgroupOf X ≤ frattini X := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff (N.subgroupOf X)).mp hb
    rw [← map_subgroupOf_eq_of_le hNX]
    exact map_mono hNphi
  · have hsup : N.subgroupOf X ⊔ frattini X = ⊤ := by
      have he := congrArg (comap q) ht
      simpa only [A, comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
    have htop : N.subgroupOf X = ⊤ := frattini_nongenerating hsup
    exact (hne (le_antisymm hNX (subgroupOf_eq_top.mp htop))).elim

/-- In either original actor alternative, a proper subgroup normal in the
actor together with the Sylow subgroup lies in the actor's Frattini subgroup. -/
theorem ActorCases.proper_normal_le_frattini {T : Sylow 2 G} {X N : Subgroup G}
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)} (hcases : ActorCases T X hTX)
    (hNX : N ≤ X) (hn : X ⊔ (T : Subgroup G) ≤ normalizer (N : Set G))
    (hne : N ≠ X) : N ≤ (frattini X).map X.subtype := by
  rcases hcases with ⟨L, hL, hX⟩ | ⟨p, hp, ho, hP, hI⟩
  · exact component_orbit_proper_normal_le_frattini hL hX hNX hn hne
  · exact hI.proper_normalized_le_frattini hNX (le_sup_right.trans hn) hne

end CFSG.Quasithin.ChapterD.Section03
