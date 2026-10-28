module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Sylow centers and marked Borels for the PSL₃ cases of E.6.11

For PSL₃(2ⁿ), the displacement has the same order as the Sylow center and
is contained in it, so the two subgroups agree. For every central two-cover
of PSL₃(4), the displacement meets the covering center trivially. Its
four-element image fills the center of the quotient Sylow subgroup; lifting
back gives the required bound by O₂(L) and the displacement.

The quotient Borel in E.6.8 is also identified with the normalizer of the
specified Sylow subgroup when Z(L) is a two-group. These deductions use the
actual component and its Sylow marking, without maximality of U or ambient
normality of L. Constructing cyclic complements remains a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and E.6.11(3b), printed pp.247–250 (PDF pp.258–261).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem sylow_center_map (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    ((center S).map (S : Subgroup L).subtype).map L.subtype =
      (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype := by
  rw [map_subgroup_center_eq L.subtype L.subtype_injective, hS]

omit [Finite G] in
/-- The moving direct factor in E.6.8 has trivial intersection with the
component center. This also proves injectivity in the central quotient. -/
theorem displacement_disjoint_center
    (b : BorelAlternative M V U L n) (hn : 1 < n) :
    ⁅V, L ⊓ M⁆ ⊓ (center L).map L.subtype = ⊥ := by
  apply le_bot_iff.mp
  rintro _ ⟨hw, z, hz, rfl⟩
  have hzC : (z : G) ∈ centralizer (L : Set G) := by
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  have hwV : (z : G) ∈ V := (le_sup_left.trans (b.decomposition hn).1.le) hw
  exact (b.decomposition hn).2.1 ▸ ⟨hw, hwV, hzC⟩

/-- The Borel supplied by E.6.8 is the normalizer of the actual marked
Sylow subgroup whenever the component center is a two-group. No ambient
normality of L is needed. -/
theorem borel_eq_sylow_normalizer
    (h : HypothesisE61 K T M V) (b : BorelAlternative M V U L n)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hz : IsPGroup 2 (center L)) :
    (L ⊓ M).subgroupOf L = normalizer (S : Set L) := by
  let q := QuotientGroup.mk' (center L)
  obtain ⟨_, R, hR⟩ := b.borel
  have hQM : Q ≤ M := by
    rw [hQ]
    exact inf_le_right.trans h.centralizer_le
  have hSB : (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L := by
    intro s hs
    have hh : (s : G) ∈ L ⊓ Q := hS ▸ mem_map_of_mem L.subtype hs
    exact ⟨s.property, hQM hh.2⟩
  have hSN : (S : Subgroup L).map q ≤ normalizer (R : Set (L ⧸ center L)) := by
    rw [map_le_iff_le_comap]
    exact hR ▸ hSB
  have hSR : (S : Subgroup L).map q ≤ (R : Subgroup (L ⧸ center L)) := by
    have hi := (S.isPGroup'.map q).inf_normalizer_sylow R
    intro x hx
    exact (hi ▸ (show x ∈ (S : Subgroup L).map q ⊓ normalizer (R : Set (L ⧸ center L))
      from ⟨hx, hSN hx⟩)).2
  have he : (R : Subgroup (L ⧸ center L)) = (S : Subgroup L).map q :=
    (S.mapSurjective (f := q) (QuotientGroup.mk'_surjective (center L))).is_maximal'
      R.isPGroup' hSR
  have hk : q.ker ≤ (S : Subgroup L) := by
    simpa only [q, QuotientGroup.ker_mk'] using hz.le_sylow_of_normal S
  rw [hR, ← Sylow.coe_coe, comap_normalizer_eq_of_surjective (R : Subgroup (L ⧸ center L))
    (QuotientGroup.mk'_surjective (center L)),
    he, comap_map_eq_self hk, Sylow.coe_coe]


/-- In the ordinary PSL₃ case the displacement is the whole Sylow center. -/
theorem center_eq_displacement_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype = ⁅V, L ⊓ M⁆ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  have hc : Nat.card (center S) = 2 ^ n :=
    Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e S
  have hcard : Nat.card ((center ↥(L ⊓ Q)).map (L ⊓ Q).subtype) = 2 ^ n := by
    rw [← sylow_center_map S hS, card_map_of_injective L.subtype_injective,
      card_map_of_injective (S : Subgroup L).subtype_injective, hc]
  symm
  apply eq_of_le_of_card_ge (displacement_le_center h hU hL hVL hQ)
  rw [hcard, displacement_card h b hn]

/-- The center bound for every central two-cover of PSL₃(4). It uses no
assumption that the covering center is a Klein four-group. -/
theorem center_le_linear_three_cover
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hn2 : n = 2) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype ≤ L.pCoreIn 2 ⊔ ⁅V, L ⊓ M⁆ := by
  let W : Subgroup G := ⁅V, L ⊓ M⁆
  let q := QuotientGroup.mk' (center L)
  have hWZ := displacement_le_center h hU hL hVL hQ
  have hWL : W ≤ L := hWZ.trans ((map_subtype_le _).trans inf_le_left)
  have hWV : W ≤ V := le_sup_left.trans (b.decomposition hn).1.le
  have hWZL : W.subgroupOf L ≤ (center S).map (S : Subgroup L).subtype := by
    intro w hw
    have hh : (w : G) ∈ ((center S).map (S : Subgroup L).subtype).map L.subtype :=
      (sylow_center_map S hS).symm ▸ hWZ hw
    obtain ⟨s, hs, he⟩ := hh
    exact L.subtype_injective he ▸ hs
  have hker : W.subgroupOf L ⊓ q.ker = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hxW, hxq⟩
    have hxZ : x ∈ center L := (QuotientGroup.ker_mk' (center L)) ▸ hxq
    have hxC : (x : G) ∈ centralizer (L : Set G) := by
      intro l hl
      exact congrArg Subtype.val (mem_center_iff.mp hxZ ⟨l, hl⟩)
    have hx : (x : G) ∈ W ⊓ (V ⊓ centralizer (L : Set G)) :=
      ⟨hxW, hWV hxW, hxC⟩
    have he : (x : G) = 1 := mem_bot.mp ((b.decomposition hn).2.1 ▸ hx)
    exact mem_bot.mpr (Subtype.ext he)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center L))
  have hc : Nat.card (center R) = 4 :=
    Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (n := 2) (by decide) hF e R
  have hcard : Nat.card (center ((S : Subgroup L).map q)) ≤ Nat.card (W.subgroupOf L) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv]
    change Nat.card (center R) ≤ Nat.card W
    rw [hc, displacement_card h b hn, hn2]
    decide
  have hcent := center_le_ker_sup_of_disjoint_of_card q (S : Subgroup L)
    (W.subgroupOf L) hWZL hker hcard
  have hzcore : center L ≤ pCore 2 L := le_sSup ⟨inferInstance, hz⟩
  have hh := map_mono (f := L.subtype) hcent
  rw [sylow_center_map S hS, Subgroup.map_sup, map_subgroupOf_eq_of_le hWL] at hh
  exact hh.trans (sup_le_sup (map_mono (by
    simpa only [q, QuotientGroup.ker_mk'] using hzcore)) le_rfl)


end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
