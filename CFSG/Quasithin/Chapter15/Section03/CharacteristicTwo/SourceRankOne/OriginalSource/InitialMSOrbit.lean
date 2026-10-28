module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Holomorph
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbitQuasisimple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.IrreducibleOmegaOrbit
public import Theory.GroupTheory.ReducedNormal.SylowCentralizer

/-!
# The initial module of the original MS pair

The actual Sylow edge centralizes precisely the two-core of its omega orbit.
Both that orbit and the central omega layer are reduced, and the latter is an
FF module on its literal centralizer quotient. The component image remains
quasisimple; no center-free or irreducible-action hypothesis is introduced.

Source: Meierfrankenfeld–Stellmacher (1993), (2.2), (3.1) and (3.2),
printed pp. 854–864; original source pair in Aschbacher–Smith 15.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension ChapterC
open MSCentralOrbit G2Holomorph
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

omit [Finite G] in
private theorem component_quotient_quasisimple :
    IsQuasisimple ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) := by
  let := c.core_quotient_quasisimple
  let e := subgroupOfEquivOfLe (component_le c)
  exact IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

include s

private theorem original_product :
    ∀ g : I, ∃ k ∈ c.L.subgroupOf I, ∃ r ∈ d.S.subgroupOf I, k*r=g := by
  let := s.normal
  have hs : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    rw [← subgroupOf_sup (component_le c)
      ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]
  intro g
  exact mem_sup_of_normal_left.mp (hs.ge (mem_top g))

private theorem original_self_centralizing :
    centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
  rw [←s.characteristicTwo]
  exact centralizer_generalizedFitting_le I

/-- The original Sylow edge has exactly its two-core as kernel on the MS orbit. -/
theorem source_ms_orbit_edge_centralizer :
    d.S.subgroupOf I ⊓ centralizer (omegaOrbit (d.S.subgroupOf I) : Set I) = pCore 2 I := by
  let := s.normal
  let := component_quotient_quasisimple (c := c)
  exact omegaOrbit_radical_centralizer (c.L.subgroupOf I) (d.S.subgroupOf I)
    (LocalData.thompson_component_in c.le_thompson c.component)
    (edge_two_group s) (edge_ne_bot s) (core_le_edge s)
    (original_self_centralizing s) (original_product s) (edge_characteristic s)

/-- The genuine Sylow orbit is reduced before any module classification. -/
theorem source_ms_orbit_reduced : IsPReduced 2 (omegaOrbit (d.S.subgroupOf I)) := by
  rw [edge_eq_sylow s]
  exact omegaOrbit_reduced s.sylow (original_self_centralizing s)

/-- The full central omega layer is also reduced; its action kernel is retained. -/
theorem source_ms_centralOmega_reduced : IsPReduced 2 (omegaCenterIn (pCore 2 I)) := by
  apply (source_ms_orbit_reduced s).of_le_of_sylow_centralizer_le s.sylow
    (omegaOrbit_le_centralOmega _ (core_le_edge s) (original_self_centralizing s))
  rw [←edge_eq_sylow s,source_ms_orbit_edge_centralizer s]
  intro z hz x hx
  exact (((mem_omegaCenterIn_iff _ _).mp hx).2.1 z hz).symm

/-- Initial FF recognition uses the actual faithful centralizer quotient. -/
theorem source_ms_centralOmega_isFFModule :
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation
        (omegaCenterIn (pCore 2 I))
        (QuotientGroup.mk' (centralizer (omegaCenterIn (pCore 2 I) : Set I)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  let := s.normal
  let := component_quotient_quasisimple (c := c)
  apply layer_isFFModule (c.L.subgroupOf I) (d.S.subgroupOf I)
    (omegaCenterIn (pCore 2 I))
    (LocalData.thompson_component_in c.le_thompson c.component)
    (edge_two_group s) (edge_ne_bot s) (core_le_edge s)
    (original_self_centralizing s) (original_product s) (edge_characteristic s)
  · exact omegaOrbit_le_centralOmega _ (core_le_edge s) (original_self_centralizing s)
  · intro x hx
    exact core_le_edge s ((mem_omegaCenterIn_iff _ _).mp hx).1

/-- The actual faithful central-omega actor retains a quasisimple component.
No trivial covering-center assumption is required. -/
theorem source_ms_centralOmega_actor_structure :
    let X := omegaCenterIn (pCore 2 I)
    let q := QuotientGroup.mk' (centralizer (X : Set I))
    let B := (c.L.subgroupOf I).map q
    IsComponent (I ⧸ centralizer (X : Set I)) B ∧
      generalizedFitting (I ⧸ centralizer (X : Set I)) = B ∧
      pCore 2 (I ⧸ centralizer (X : Set I)) = ⊥ := by
  dsimp only
  let K := c.L.subgroupOf I
  let R := d.S.subgroupOf I
  let X := omegaCenterIn (pCore 2 I)
  let q := QuotientGroup.mk' (centralizer (X : Set I))
  let B := K.map q
  let := s.normal
  let : K.Normal := s.normal
  let := component_quotient_quasisimple (c := c)
  have hK : K.IsCComponent := LocalData.thompson_component_in c.le_thompson c.component
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hQC : pCore 2 I ≤ centralizer (X : Set I) := by
    intro z hz x hx
    exact (((mem_omegaCenterIn_iff _ _).mp hx).2.1 z hz).symm
  have hkill : K.pCoreIn 2 ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (pCoreIn_le_of_subnormal 2 hK.subnormal).trans hQC
  have hBne : B ≠ ⊥ := by
    intro hz
    have hKC : K ≤ centralizer (X : Set I) := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
    exact component_not_centralizes_omegaOrbit K R (edge_two_group s) (edge_ne_bot s)
      (original_product s) (edge_characteristic s)
      (hKC.trans (centralizer_le (omegaOrbit_le_centralOmega _
        (core_le_edge s) (original_self_centralizing s))))
  have hB : IsComponent _ B :=
    hK.isComponent_map_of_twoCore_killed inferInstance q hq hkill hBne
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let : IsQuasisimple B := hB.2
  have hsup : B ⊔ R.map q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g,rfl⟩ := hq x
    obtain ⟨k,hk,r,hr,rfl⟩ := original_product s g
    rw [map_mul]
    exact mul_mem ((show B ≤ B ⊔ R.map q from le_sup_left) (mem_map_of_mem q hk))
      ((show R.map q ≤ B ⊔ R.map q from le_sup_right) (mem_map_of_mem q hr))
  have hcore := (source_ms_centralOmega_reduced s).quotient_pCore_eq_bot
  exact ⟨hB,generalizedFitting_eq_of_quasisimple_two_quotient B
    (isPGroup_quotient_of_sup_eq_top B (R.map q) ((edge_two_group s).map q) hsup) hcore,hcore⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
