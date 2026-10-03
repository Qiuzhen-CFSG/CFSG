module

public import ABG.ChapterII.Section2.WeakCenterTransport
public import ABG.ChapterII.Section3.CoreFreeWeakCenter
public import ABG.ChapterII.Section3.OddCoreReduction

/-!
# A Q-group centralizes its Sylow center modulo the odd core

For every Sylow two-subgroup S of a finite Q-group G, the odd core together
with the centralizer of Z(S) generates G. The enlarged Q-group predicate
supplies weak closure of every subgroup of Z(S), for the arbitrary chosen S.

Pass to G/O(G). The image T of Z(S) lies in and centralizes the image Sylow
subgroup, and all subgroups of T remain weakly closed. The quotient has
trivial odd core, so the central-quotient argument in CoreFreeWeakCenter makes
T central, using the proved Glauberman Z-star theorem. Coprime centralizer
lifting through the odd core now gives the required supplement.

This is ABG Chapter II, Section 3, Proposition 1, article pages 21-22:
`refs/latex/alperin-brauer-gorenstein-pages/page-022.tex` and `page-023.tex`.
Only the image of the original center is used; no quotient-center equality
or additional Q-group hypothesis is assumed.
-/

public section
namespace ABG

theorem qGroup_eq_oddCore_mul_sylowCenterCentralizer
    {G : Type*} [Group G] [Finite G] (hQ : IsQGroup G) (S : Sylow 2 G) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer (subgroupCenter (S : Subgroup G) : Set G) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := subgroupCenter (S : Subgroup G)
  have hZS : Z ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hZC : Z ≤ Subgroup.centralizer (S : Set G) := by
    rintro x ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
  have hZtwo : IsPGroup 2 Z := S.isPGroup'.to_le hZS
  let q := QuotientGroup.mk' (pPrimeCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pPrimeCore 2 G)
  let Sbar := S.mapSurjective (f := q) hq
  let T := Z.map q
  have hSbar : (Sbar : Subgroup (G ⧸ pPrimeCore 2 G)) = (S : Subgroup G).map q :=
    Sylow.coe_mapSurjective _ _
  have hTS : T ≤ (Sbar : Subgroup (G ⧸ pPrimeCore 2 G)) := by
    rw [hSbar]
    exact Subgroup.map_mono hZS
  have hTC : T ≤ Subgroup.centralizer (Sbar : Set (G ⧸ pPrimeCore 2 G)) := by
    rintro x ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ (Sbar : Subgroup (G ⧸ pPrimeCore 2 G)) at hy
    rw [hSbar] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact congrArg q (Subgroup.mem_centralizer_iff.mp (hZC hz) s hs)
  have hweak : ∀ J ≤ T,
      BenderSuzuki.External.WeaklyClosedIn (Sbar : Subgroup (G ⧸ pPrimeCore 2 G)) J := by
    intro J hJ
    rw [hSbar]
    exact (hQ.hasWeaklyClosedCenterSubgroups S).weaklyClosedIn_of_le_map q hq J hJ
  apply oddCore_sup_centralizer_eq_top_of_image_le_center Z hZtwo
  exact le_center_of_weakly_closed_subgroups_of_oddCore_eq_bot
    Sbar T hTS hTC hweak (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))

end ABG
