module
public import Stellmacher.SectionNine.NineEightInitialExtraction
public import Stellmacher.SectionNine.NineEightReverseNeighborhood

/-!
# Prescribed-pair and symmetric crossing extractions in Stellmacher (9.8)

The proved initial extraction transfers to any commuting critical pair
with a prescribed first neighbor and the terminal-center containment.
The output retains the index-two W/stabilizer intersection, the escaping
initial center and nontrivial center commutator, and generation by every
subgroup of W crossing the new edge. A specialization applies this to
the reversed pair consisting of an escaping terminal neighbor and the
original first-step vertex.

Prescribed-edge normalization transports all three supplied vertices by
one actor. Conjugation preserves W, subgroup intersections, cardinalities,
commutators and generated joins, so all extraction conclusions pull back.
For the reversed pair, critical minimality supplies exact distance and
the two centers commute inside the elementary terminal module.
The universal generation clause is needed again at the end of (9.8):
a replacement terminal-neighbor center lies in Vterminal≤Wm.

Source: Stellmacher (9.8), printed pp.55–56/PDF pp.45–46, the symmetric
extraction and the final equality of generated subgroups.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_crossing_extraction_of_critical_pair
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (left right prescribed : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hadj : ctx.Γ.adjacent left prescribed)
    (hdistance : ctx.Γ.distance left right = ctx.Γ.distance prescribed right + 1)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ = ⊥)
    (hcontain : ZAt ctx.Γ right ≤ VAt ctx.Γ prescribed) :
    ∃ extracted : ctx.Γ.Vertex,
      extracted ∈ Neighborhood ctx.Γ right ∧
      QuotientCardEq (GeneratedNeighborhoodV ctx.Γ left)
        (GeneratedNeighborhoodV ctx.Γ left ⊓ GAt ctx.Γ extracted) 2 ∧
      (¬ ZAt ctx.Γ left ≤ GAt ctx.Γ extracted) ∧
      ⁅ZAt ctx.Γ left,ZAt ctx.Γ extracted⁆ ≠ ⊥ ∧
      (∀ support : Subgroup G, support ≤ GeneratedNeighborhoodV ctx.Γ left →
        (¬ support ≤ GAt ctx.Γ extracted) →
        (GAt ctx.Γ right ⊓ GAt ctx.Γ extracted) ⊔ support = GAt ctx.Γ right) := by
  let Γ := ctx.Γ
  obtain ⟨actor, path, hleft, hright, hnext, hlength⟩ :=
    exists_criticalPath_of_critical_pair_through_neighbor ctx.sectionSeven Γ ctx.criticalPath left
      right prescribed hcritical hadj hdistance
  have hpathComm : ⁅Γ.z path.a, Γ.z path.a'⁆ = ⊥ := by
    rw [hleft,hright,z_act,z_act,← Subgroup.map_commutator]
    change (⁅ZAt Γ left,ZAt Γ right⁆).map _ = ⊥
    rw [hcomm,Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := path, commutator_eq := hpathComm }
  have hpathContain : ZAt Γ path.a' ≤ VAt Γ path.firstStep := by
    change z Γ path.a' ≤ v Γ path.firstStep
    rw [hright,hnext,z_act,v_act]
    exact Subgroup.map_mono hcontain
  obtain ⟨next,hnextNeighbor,hindex,hnotNext,hnoncomm,hgenerate⟩ :=
    nine_eight_initial_crossing_extraction shifted
      (by change 3 < path.length; rwa [hlength]) hpathContain
  let actual := Γ.act actor⁻¹ next
  have hactual : Γ.act actor actual = next := by
    dsimp only [actual]
    rw [← Γ.act_mul,inv_mul_cancel,Γ.act_one]
  have hactualNeighbor : actual ∈ Neighborhood Γ right := by
    have hh := adjacent_act Γ actor⁻¹ ((mem_neighborhood_iff_adjacent Γ).mp hnextNeighbor)
    change Γ.adjacent (Γ.act actor⁻¹ path.a') actual at hh
    rw [hright,← Γ.act_mul,mul_inv_cancel,Γ.act_one] at hh
    exact (mem_neighborhood_iff_adjacent Γ).mpr hh
  refine ⟨actual,hactualNeighbor,?_,?_,?_,?_⟩
  · change Nat.card (GeneratedNeighborhoodV Γ path.a) =
      2 * Nat.card (GeneratedNeighborhoodV Γ path.a ⊓ GAt Γ next : Subgroup G) at hindex
    change Nat.card (GeneratedNeighborhoodV Γ left) =
      2 * Nat.card (GeneratedNeighborhoodV Γ left ⊓ GAt Γ actual : Subgroup G)
    rw [hleft,← hactual,nine_seven_neighborhood_act] at hindex
    change Nat.card ((GeneratedNeighborhoodV Γ left).map (MulAut.conj actor⁻¹).toMonoidHom) =
      2 * Nat.card ((GeneratedNeighborhoodV Γ left).map (MulAut.conj actor⁻¹).toMonoidHom ⊓
        stabilizer Γ (Γ.act actor actual) : Subgroup G) at hindex
    rw [stabilizer_act,conjugateBy,← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective] at hindex
    exact hindex
  · intro hle
    apply hnotNext
    change z Γ path.a ≤ stabilizer Γ next
    rw [hleft,← hactual,z_act,stabilizer_act]
    exact Subgroup.map_mono hle
  · intro hzero
    apply hnoncomm
    change ⁅z Γ path.a,z Γ next⁆ = ⊥
    rw [hleft,← hactual,z_act,z_act,← Subgroup.map_commutator]
    change (⁅ZAt Γ left,ZAt Γ actual⁆).map _ = ⊥
    rw [hzero,Subgroup.map_bot]
  · intro support hsupport hsupportNot
    let mapped := support.map (MulAut.conj actor⁻¹).toMonoidHom
    have hsupportPath : mapped ≤ GeneratedNeighborhoodV Γ path.a := by
      rw [hleft,nine_seven_neighborhood_act]
      exact Subgroup.map_mono hsupport
    have hsupportNotPath : ¬ mapped ≤ GAt Γ next := by
      intro hle
      apply hsupportNot
      change mapped ≤ stabilizer Γ next at hle
      rw [← hactual,stabilizer_act] at hle
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle
    have hgenerated := hgenerate mapped hsupportPath hsupportNotPath
    change (stabilizer Γ path.a' ⊓ stabilizer Γ next) ⊔ mapped =
      stabilizer Γ path.a' at hgenerated
    rw [hright,← hactual,stabilizer_act,stabilizer_act,conjugateBy,conjugateBy,
      ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective] at hgenerated
    change ((GAt Γ right ⊓ GAt Γ actual).map (MulAut.conj actor⁻¹).toMonoidHom) ⊔
      support.map (MulAut.conj actor⁻¹).toMonoidHom =
      (GAt Γ right).map (MulAut.conj actor⁻¹).toMonoidHom at hgenerated
    rw [← Subgroup.map_sup] at hgenerated
    exact (Subgroup.map_injective (MulAut.conj actor⁻¹).injective) hgenerated

public theorem nine_eight_reverse_crossing_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hreverse : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a')
    (hescape : ¬ ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a) :
    ∃ next : ctx.Γ.Vertex,
      next ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
      QuotientCardEq (GeneratedNeighborhoodV ctx.Γ neighbor)
        (GeneratedNeighborhoodV ctx.Γ neighbor ⊓ GAt ctx.Γ next) 2 ∧
      (¬ ZAt ctx.Γ neighbor ≤ GAt ctx.Γ next) ∧
      ⁅ZAt ctx.Γ neighbor,ZAt ctx.Γ next⁆ ≠ ⊥ ∧
      (∀ support : Subgroup G, support ≤ GeneratedNeighborhoodV ctx.Γ neighbor →
        (¬ support ≤ GAt ctx.Γ next) →
        (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ next) ⊔ support =
          GAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hnot : ¬ ZAt Γ neighbor ≤ QAt Γ cp.firstStep := by
    intro hle
    exact hescape (hle.trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      cp.firstStep cp.a ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm cp.firstStep_adj)) default).2.2))
  have htail : Γ.distance cp.a' cp.firstStep ≤ cp.length - 1 := by
    have hpath := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [Γ.distance_symm]
    simpa only [cp.path_first,cp.path_end] using hpath
  have hadj : Γ.adjacent neighbor cp.a' := Γ.adjacent_symm
    ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hupper := nine_eight_adjacent_distance_le Γ hadj (target := cp.firstStep)
  have hlower : cp.length ≤ Γ.distance neighbor cp.firstStep := by
    by_contra hlt
    exact hnot (critical_minimality Γ cp (by omega))
  have hdistance : Γ.distance neighbor cp.firstStep = cp.length := by omega
  have hcritical : IsCriticalPair Γ neighbor cp.firstStep := by
    refine ⟨?_,hnot⟩
    rw [hdistance,← cp.endpoint_distance]
    exact cp.critical.1
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hlong).2.2.1
  have hcomm : ⁅ZAt Γ neighbor,ZAt Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hneighborV.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le hreverse)))
  exact nine_eight_crossing_extraction_of_critical_pair ctx hb neighbor cp.firstStep cp.a'
    hcritical hadj (by change Γ.distance neighbor cp.firstStep = Γ.distance cp.a' cp.firstStep + 1; omega)
    hcomm hreverse

end Stellmacher.SectionNine
