module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Seed
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair
public import Theory.GroupTheory.PResidual.Restriction

/-!
# The literal diagonal stabilizer and its residual

The candidate parabolic is C_{L₀T}(z). Since L₀ is normal in L₀T with
two-group quotient, its intersection with any point centralizer contains
the latter's two-residual. Restriction of residuals therefore identifies
O²(C_{L₀T}(z)) with the original O²(C_{L₀}(z)). If z centralizes T,
the Sylow supplement then gives C_{L₀T}(z)=XT.

For the original diagonal involution this subgroup has a nontrivial
two-core, and the zero full fixed part makes it proper in L₀T. Maximality
and the actual quotient model are separate natural-action calculations.

Source: Aschbacher--Smith 10.2.4, 10.2.11 and §10.3,
printed pp.747,753--754,756--757.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The source point stabilizer, inside the original Sylow-component join. -/
def diagonalParabolic (T : Sylow 2 G) (L : Subgroup G) (z : G) : Subgroup G :=
  localJoin T L ⊓ centralizer ({z} : Set G)

omit [Finite G] in
theorem diagonalParabolic_le_join (z : G) :
    diagonalParabolic T L z ≤ localJoin T L := inf_le_left

omit [Finite G] in
theorem sylow_le_diagonalParabolic {z : G}
    (hz : z ∈ centerIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ diagonalParabolic T L z := by
  refine le_inf le_sup_right ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (hz.2 t ht)

/-- This residual equality needs no recognition of the point stabilizer. -/
theorem diagonalParabolic_residual (z : G) :
    (pResidual 2 (diagonalParabolic T L z)).map
      (diagonalParabolic T L z).subtype = centralizerSeed T L z := by
  let J := localJoin T L
  let R := (localOrbit T L).subgroupOf J
  have hRJ : localOrbit T L ≤ J := le_sup_left
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hgen : R ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRJ,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsPGroup 2 (J ⧸ R) :=
    isPGroup_quotient_of_sup_eq_top R ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  have hres : (pResidual 2 J).map J.subtype ≤ localOrbit T L := by
    rintro x ⟨y,hy,rfl⟩
    exact (show pResidual 2 J ≤ R from sInf_le ⟨inferInstance,hq⟩) hy
  symm
  apply embedded_pResidual_eq_of_le_of_residual_le 2
    (inf_le_inf_right _ hRJ)
  exact le_inf
    ((embedded_pResidual_mono 2 (diagonalParabolic_le_join z)).trans hres)
    ((map_subtype_le _).trans inf_le_right)

/-- The candidate is exactly the seed-Sylow join used by all later consumers. -/
theorem seed_join_eq_diagonalParabolic {z : G}
    (hz : z ∈ centerIn (T : Subgroup G)) :
    centralizerSeed T L z ⊔ (T : Subgroup G) = diagonalParabolic T L z := by
  have he := congrArg (map (diagonalParabolic T L z).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (sylow_le_diagonalParabolic hz)))
  simpa only [Subgroup.map_sup, diagonalParabolic_residual, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le (sylow_le_diagonalParabolic hz),
    ← MonoidHom.range_eq_map, range_subtype] using he

omit [Finite G] in
/-- The central involution witnesses membership in the actual family H. -/
theorem diagonalParabolic_mem_H {z : G}
    (hz : z ∈ centerIn (T : Subgroup G)) (ho : orderOf z = 2) :
    diagonalParabolic T L z ∈ Chapter1.H G := by
  let P := diagonalParabolic T L z
  let Z := zpowers z
  have hZ : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    simpa only [Z, Nat.card_zpowers, pow_one] using ho)
  have hZP : Z ≤ P := zpowers_le.mpr (sylow_le_diagonalParabolic hz hz.1)
  have hPC : P ≤ centralizer (Z : Set G) := by
    dsimp only [Z]
    rw [zpowers_eq_closure, centralizer_closure]
    exact inf_le_right
  have hcore := le_pCoreIn_of_normalizes hZ hZP
    (hPC.trans (Subgroup.centralizer_le_normalizer _))
  change P.pCoreIn 2 ≠ ⊥
  intro hbot
  have hone : z = 1 := mem_bot.mp (hbot ▸ hcore (mem_zpowers z))
  rw [hone,orderOf_one] at ho
  omega

/-- Properness follows already from the original full fixed-part hypothesis. -/
theorem diagonalParabolic_lt_join
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {s : SourceLinearThreeSurvivor T D} (d : CentralizerData T D s) :
    diagonalParabolic T L (d.first*d.second) < localJoin T L := by
  apply lt_of_le_of_ne (diagonalParabolic_le_join _) ?_
  intro he
  have hJC : localJoin T L ≤ centralizer ({d.first*d.second} : Set G) :=
    he ▸ (inf_le_right : diagonalParabolic T L (d.first*d.second) ≤ _)
  have hfixed : d.first*d.second ∈ D.fullModule ⊓
      centralizer (localOrbit T L : Set G) := by
    refine ⟨D.fullModule.mul_mem (survivor_moved_le s d.first_mem)
      (survivor_partner_le s d.second_mem), ?_⟩
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hJC (mem_sup_left hx))
  have hone : d.first*d.second = 1 := mem_bot.mp (d.fixed_part ▸ hfixed)
  have ho := d.order
  rw [hone,orderOf_one] at ho
  omega

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
