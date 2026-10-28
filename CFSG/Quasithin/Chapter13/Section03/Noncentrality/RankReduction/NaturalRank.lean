module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalIntersection
public import Theory.GroupTheory.PrimeRankNormalPair
/-!
# Odd rank of the original natural centralizing residual

The cubic plane image supplies an actual odd mover. Its two residual
conjugates normalize one another inside C(V₂), and their intersection is
a two-group. Rank addition and the original quasithin local bound force
each odd rank to be at most one. No conjugate-intersection or rank
conclusion is assumed. Earlier chosen-module TI, normalizer placement and
maximal-local uniqueness remain the exact source inputs.
Source: Aschbacher–Smith 13.3.14(b), printed p.891.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d
/-- The same residual and its plane-normalizing conjugate mutually normalize inside C(V₂). -/
theorem natural_residual_conjugate_local_data (g : G)
    (hgE : g ∈ normalizer (E : Set G)) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    let Yg := Y.map (MulAut.conj g).toMonoidHom
    Y ⊔ Yg ≤ centralizer (E : Set G) ∧
      Y ≤ normalizer (Yg : Set G) ∧ Yg ≤ normalizer (Y : Set G) := by
  let Y := centralizingResidual (conjugateSpanBy U H)
  let c := (MulAut.conj g).toMonoidHom
  let Yg := Y.map c
  have hYE : Y ≤ centralizer (E : Set G) :=
    (centralizingResidual_le_seed_centralizer U H).trans (centralizer_le d.plane_le_seed)
  have hCEH : centralizer (E : Set G) ≤ H := by
    rw [d.first_normalizer]
    exact (centralizer_le d.line_le_plane).trans (Subgroup.centralizer_le_normalizer _)
  have hHY := normalizes_centralizingResidual U H
  have hn : g ∈ normalizer (centralizer (E : Set G) : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp
      inferInstance) hgE
  have hYgE : Yg ≤ centralizer (E : Set G) :=
    (map_mono (f := c) hYE).trans_eq ((mem_normalizer_iff_map_conj_eq).mp hn)
  have hYgN : Yg ≤ normalizer (Y : Set G) := hYgE.trans (hCEH.trans hHY)
  have hYNg : Y ≤ normalizer (Yg : Set G) := by
    have hc : centralizer (E : Set G) ≤ H.map c := by
      rw [← (mem_normalizer_iff_map_conj_eq).mp hn]
      exact map_mono hCEH
    exact (hYE.trans hc).trans ((map_mono (f := c) hHY).trans (le_normalizer_map c))
  exact ⟨sup_le hYE hYgE,hYNg,hYgN⟩

/-- The actual centralizing residual has rank at most one at every odd prime. -/
theorem natural_residual_odd_rank [Group.IsPerfect L]
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hNVL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (centralizingResidual (conjugateSpanBy U H)) ≤ 1 := by
  let := Fact.mk hp
  obtain ⟨g,hg,hodd,hgE,_,hjoin⟩ := natural_odd_plane_mover d X hXL hx
  let Y := centralizingResidual (conjugateSpanBy U H)
  let Yg := Y.map (MulAut.conj g).toMonoidHom
  have hi := natural_residual_intersection_isTwoGroup d hTI hNVL hunique hescape
    ⟨g,hXL hg⟩ hgE hjoin
  obtain ⟨hlocal,hYYg,hYgY⟩ := natural_residual_conjugate_local_data d g hgE
  have hr := Theory.GroupTheory.primeRank_add_le_of_normalizes_of_twoGroup_intersection
    ho Y Yg hYYg hYgY hi
  have he : primeRank p Yg = primeRank p Y :=
    (primeRank_congr p (Y.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm
  have hne : E ≠ ⊥ := by intro h; have hc := d.plane_card; simp [h] at hc
  have htwo : IsPGroup 2 E := IsPGroup.of_card (n := 2) d.plane_card
  have hbound := isQuasithin_iff_twoLocal.mp d.counterexample.qtke.quasithin
      (normalizer (E : Set G)) ⟨E,hne,htwo,rfl⟩ p hp ho
  have hmono : primeRank p (Y ⊔ Yg : Subgroup G) ≤ primeRank p (normalizer (E : Set G)) :=
    primeRank_mono p (hlocal.trans (Subgroup.centralizer_le_normalizer _))
  have hh : 2 * primeRank p Y ≤ 2 := calc
    _ = primeRank p Y + primeRank p Yg := by omega
    _ ≤ primeRank p (Y ⊔ Yg : Subgroup G) := hr
    _ ≤ primeRank p (normalizer (E : Set G)) := hmono
    _ ≤ 2 := hbound
  change primeRank p Y ≤ 1
  omega
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
