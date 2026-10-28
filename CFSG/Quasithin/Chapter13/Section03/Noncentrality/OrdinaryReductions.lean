module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalSolvable
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.F9Application
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual

/-!
# The first ordinary-source reductions of 13.3.14

The original natural A₆ configuration supplies the elementary flag,
characteristic-two point normalizer, TI property, and unique maximal local
overgroup. Thus centralization of the plane gives reduction (a), while
nonabelianness of the full V-span gives the escape needed for reduction (b).
The latter bounds the actual two-residual of the seed-span centralizer and
forces every odd rank-two star residual to move that span.

These are the first reductions of the noncentrality proof; neither F.9
nor plane noncentrality is assumed to obtain the escape and rank bounds.
Source: Aschbacher–Smith, 13.3.14(a–b), printed pp.891–892.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- Nonabelianness of the original full span forces the actual point
normalizer outside the original local normalizer. -/
theorem ordinary_point_not_le_local
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H)) : ¬ H ≤ M := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,U,P,H⟩
  have he : H = D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two P d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have dd : NaturalSetup D.T D.L D.V D.V₁ E D.Vplus M D.Gz := he ▸ d
  have hv : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz) := he ▸ hV
  have hh := Section07.OrdinarySource.point_normalizer_mem_Hz_of_nonabelian_full
    dd h1221 hv
  exact he ▸ hh.2.2

/-- Reduction (a) on the actual ordinary flag. -/
theorem ordinary_reduction_a (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) :
    conjugateSpanBy U H = conjugateSpanBy E H ∧
      conjugateSpanBy U H ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2) := by
  let := d.chosen.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (d.plane_le_seed.trans d.seed_le)
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hP : P ≠ ⊥ := by
    intro he
    have hh := d.line_card
    simp [he] at hh
  have hH : H ∈ Chapter1.He G := by
    apply Chapter1.twoLocal_mem_He_of_sylow_le T
      (d.counterexample.qtke.evenCharacteristic T) _ hTH
    rw [d.first_normalizer]
    exact ⟨P,hP,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  apply reduction_a E U (sourceOne L T P) H
    (d.plane_le_seed.trans (d.seed_le.trans (d.chosen.le_sylow.trans hTH)))
    (d.first_normalizer ▸ (one_le L T P).trans inf_le_right)
    (Section07.ModelExclusions.plane_orbit_point_residual d).symm hH
  rwa [commutator_comm]

/-- Reduction (b), before supplying the full-span escape. -/
theorem ordinary_reduction_b
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hc : V ⊓ centralizer (L : Set G) = ⊥ := by
    have hh := congrArg (Subgroup.map V.subtype)
      (Section07.ModelExclusions.NaturalModels.centralizer_bot d)
    change ((centralizer (L : Set G)).subgroupOf V).map V.subtype =
      (⊥ : Subgroup V).map V.subtype at hh
    rwa [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] at hh
  have hTI := d.chosen.ti_of_centralizer_eq_bot h1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc
  have hNVL : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    h1221.normal_subgroup_normalizer_le d.normalizes_L
      (d.chosen.le_sylow.trans le_sup_right) d.chosen.ne_bot d.normalizes_V
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have horb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
    simpa only [horb,←d.local_normalizer] using hu.normalizer_unique
  obtain ⟨hx,_⟩ := Section05.PlaneGeometry.TwoBlocks.Ordinary.planeActor_action_source d e
  exact natural_residual_solvable_and_odd_rank d hTI hNVL huniq hescape
    (Section05.PlaneGeometry.TwoBlocks.planeActor (L := L) (V₂ := E))
    (Section05.PlaneGeometry.TwoBlocks.planeActor_le.trans inf_le_left) hx

/-- Reduction (b) using precisely the full-span hypothesis of 13.7. -/
theorem ordinary_reduction_b_of_nonabelian_full
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H)) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 :=
  ordinary_reduction_b d e h1221 (ordinary_point_not_le_local d h1221 hV)

/-- Literal application of reduction (b) to the residual preimage used in
13.3.14(d); the projection is the original H → H/O₂(H). -/
theorem ordinary_starResidual_moves
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (D : Subgroup (Star H)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hD : IsPGroup p D) (hr : 1 < primeRank p D) :
    ⁅conjugateSpanBy U H,(starResidual H D).map H.subtype⁆ ≠ ⊥ :=
  starResidual_moves_of_rank H _ D hp hD hr
    ((ordinary_reduction_b_of_nonabelian_full d e h1221 hV).2 p Fact.out hp)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
