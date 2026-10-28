module

public import Glauberman.ZStar
public import ABG.ChapterII.Section3.CoreFreeCentralQuotient
public import ABG.ChapterII.Section3.WeakCenterQuotient
public import Theory.GroupTheory.CentralLiftFromSylow

/-!
# Centrality from weak closure in an odd-core-free group

Let T lie in and centralize a Sylow two-subgroup of a finite group with
trivial odd core. If every subgroup of T is weakly closed in that Sylow
subgroup, then T is central in the ambient group.

Set N = T intersect Z(G). The image of T modulo N is a two-group; if it is
nontrivial, choose a subgroup of order two. Weak closure descends through
the quotient. The central-two-quotient odd-core theorem and Glauberman's
proved Z-star theorem make this subgroup central. Centrality lifts for its
preimages in T because they already centralize a Sylow subgroup, so the
order-two subgroup is trivial, a contradiction.

This isolates the central-quotient argument of ABG Chapter II, Section 3,
Proposition 1, article pages 21-22 (`page-022.tex` and `page-023.tex`). It is
stated for arbitrary T so the final application can use the image of the
original Sylow center without asserting that every quotient center lifts.
-/

public section
namespace ABG

private theorem weaklyClosedIn_of_all_subgroups_of_le_map
    {G H : Type*} [Group G] [Finite G] [Group H]
    (S : Sylow 2 G) (T : Subgroup G)
    (hweak : ∀ J ≤ T, BenderSuzuki.External.WeaklyClosedIn (S : Subgroup G) J)
    (q : G →* H) (hq : Function.Surjective q)
    (Z : Subgroup H) (hZ : Z ≤ T.map q) :
    BenderSuzuki.External.WeaklyClosedIn ((S : Subgroup G).map q) Z := by
  let J : Subgroup G := Z.comap q ⊓ T
  have hJ := hweak J inf_le_right
  have hmap : J.map q = Z := by
    apply le_antisymm
    · rintro z ⟨j, hj, rfl⟩
      exact hj.1
    · intro z hz
      obtain ⟨j, hj, hjz⟩ := hZ hz
      exact ⟨j, ⟨by simpa [Subgroup.mem_comap, hjz] using hz, hj⟩, hjz⟩
  rw [← hmap]
  refine ⟨Subgroup.map_mono hJ.1, ?_⟩
  intro b hb
  change (J.map q).map (MulAut.conj b⁻¹).toMonoidHom ≤ (S : Subgroup G).map q at hb
  change (J.map q).map (MulAut.conj b⁻¹).toMonoidHom = J.map q
  apply weakly_closed_map_of_surjective S J hJ.1 ?_ q hq b⁻¹ hb
  intro g hg
  simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using
    (hJ.2 g⁻¹ (by
      simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hg))

theorem le_center_of_weakly_closed_subgroups_of_oddCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G))
    (hTC : T ≤ Subgroup.centralizer (S : Set G))
    (hweak : ∀ J ≤ T, BenderSuzuki.External.WeaklyClosedIn (S : Subgroup G) J)
    (hcore : pPrimeCore 2 G = ⊥) : T ≤ Subgroup.center G := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := T ⊓ Subgroup.center G
  have hNcent : N ≤ Subgroup.center G := inf_le_right
  let : N.Normal := ⟨fun x hx g => by
    simpa [Subgroup.mem_center_iff.mp (hNcent hx) g] using hx⟩
  have hTp : IsPGroup 2 T := S.isPGroup'.to_le hTS
  have hNp : IsPGroup 2 N := hTp.to_le inf_le_left
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let U : Subgroup (G ⧸ N) := T.map q
  by_contra hnot
  have hUne : U ≠ ⊥ := by
    intro hU
    have hTN : T ≤ N := by
      simpa [U, q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff T).mp hU
    exact hnot (hTN.trans hNcent)
  have hUp : IsPGroup 2 U := hTp.map q
  obtain ⟨Z', hZ'card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hUp
      (n := 1) (by
        simpa only [pow_one] using Nat.succ_le_of_lt (U.one_lt_card_iff_ne_bot.mpr hUne))
  let Z : Subgroup (G ⧸ N) := Z'.map U.subtype
  have hZU : Z ≤ U := Subgroup.map_subtype_le Z'
  have hZcard : Nat.card Z = 2 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    simpa using hZ'card
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hZweak : BenderSuzuki.External.WeaklyClosedIn (Sbar : Subgroup (G ⧸ N)) Z := by
    simpa [Sbar, Sylow.coe_mapSurjective] using
      weaklyClosedIn_of_all_subgroups_of_le_map S T hweak q
        (QuotientGroup.mk'_surjective N) Z hZU
  have hbarcore : pPrimeCore 2 (G ⧸ N) = ⊥ :=
    oddCore_quotient_eq_bot_of_central_two_subgroup N hNcent hNp hcore
  have hZcent : Z ≤ Subgroup.center (G ⧸ N) := by
    have hstar := Glauberman.weaklyClosedInvolution_le_center_quotient_oddCore
      Sbar Z hZcard hZweak
    let r := QuotientGroup.mk' (pPrimeCore 2 (G ⧸ N))
    have hr : Function.Injective r := by
      apply (MonoidHom.ker_eq_bot_iff r).mp
      simpa [r, QuotientGroup.ker_mk'] using hbarcore
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply hr
    simpa only [map_mul] using
      Subgroup.mem_center_iff.mp (hstar (Subgroup.mem_map_of_mem r hz)) (r g)
  have hZbot : Z = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨x, hxT, rfl⟩ := hZU hz
    have hxcenter : x ∈ Subgroup.center G :=
      Subgroup.mem_center_of_quotient_mem_center_of_centralizes_sylow
        N hNcent hNp S (hTC hxT) (hZcent hz)
    have hxN : x ∈ N := ⟨hxT, hxcenter⟩
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff (N := N) x).mpr hxN
    simp [hxq]
  rw [hZbot, Subgroup.card_bot] at hZcard
  contradiction

end ABG
