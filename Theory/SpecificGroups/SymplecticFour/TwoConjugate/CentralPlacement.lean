module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingActor
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterPlacement

/-!
# Central placement from a diagram-moving Sylow actor

Every elementary subgroup of the standard Sylow lies in one of its two
parabolic radicals. A genuine diagram-moving automorphism normalizing the
Sylow exchanges these radicals: its inner factor lies in the Borel and its
field factor preserves both. Setwise stability therefore places V in their
intersection, the actual Sylow center. This is the first Sp4 step of E.2.7,
printed p.219; no pointwise fixedness or prescribed root placement is assumed.
-/

@[expose] public section
noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
open EvenBorelTorus EvenBorelTorus.ActorReduction CentralRootGeometry
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
omit [CharP F 2] [Finite F] in
private theorem map_embedded_core {P : Subgroup (Sp F)} (τ : MulAut (Sp F)) :
    ((pCore 2 P).map P.subtype).map τ.toMonoidHom =
      (pCore 2 (P.map τ.toMonoidHom)).map (P.map τ.toMonoidHom).subtype := by
  let e := P.equivMapOfInjective τ.toMonoidHom τ.injective
  rw [← pCore_map_iso 2 e, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem field_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (σ : F ≃+* F) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      (fieldAutomorphism σ).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient =
      (pCore 2 pointParabolic).map pointParabolic.subtype from
      (pointParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [field_map_pointParabolic]

private theorem graph_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      graphAut.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient =
      (pCore 2 pointParabolic).map pointParabolic.subtype from
      (pointParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [graphAut_map_point]
  exact planeParabolic_core_map_eq_radical hF hn

private theorem graph_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      graphAut.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient =
      (pCore 2 planeParabolic).map planeParabolic.subtype from
      (planeParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [graphAut_map_plane]
  exact pointParabolic_core_map_eq_radical hF hn

private theorem field_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (σ : F ≃+* F) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      (fieldAutomorphism σ).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient =
      (pCore 2 planeParabolic).map planeParabolic.subtype from
      (planeParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [field_map_planeParabolic]

private theorem conj_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {g : Sp F} (hg : g ∈ borel) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      (MulAut.conj g).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [pointRadicalAmbient_normalizer hF hn]
  exact (show g ∈ pointParabolic from hg.1)

private theorem conj_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {g : Sp F} (hg : g ∈ borel) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      (MulAut.conj g).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [planeRadicalAmbient_normalizer hF hn]
  exact (show g ∈ planeParabolic from hg.2)


/-- A moving automorphism fixing the Sylow exchanges its actual parabolic
radicals. The inner factor is kept in the Borel normalizer. -/
theorem moving_swaps_radicals {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:MulAut (Sp F)) (hU:unipotent.map a.toMonoidHom=unipotent)
    (ha:¬PreservesDiagram a) :
    pointRadicalAmbient.map a.toMonoidHom=planeRadicalAmbient ∧
      planeRadicalAmbient.map a.toMonoidHom=pointRadicalAmbient := by
  obtain ⟨g,σ,hnorm⟩ := SymplecticConjugatePair.Ambient.moving_eq_inner_field_graph a ha
  have hfieldU : unipotent.map (fieldAutomorphism σ).toMonoidHom = unipotent := by
    rw [unipotent,map_inf _ _ _ (fieldAutomorphism σ).injective,
      pointLocal_map hF hn (fieldAutomorphism σ) (field_map_pointParabolic σ),
      planeLocal_map hF hn (fieldAutomorphism σ) (field_map_planeParabolic σ)]
  have hgB : g∈borel := by
    rw [borel_eq_normalizer_unipotent,mem_normalizer_iff_map_conj_eq]
    have hh:=hU
    rw [hnorm] at hh
    change unipotent.map ((MulAut.conj g).toMonoidHom.comp
      ((fieldAutomorphism σ).toMonoidHom.comp graphAut.toMonoidHom))=unipotent at hh
    rw [←map_map,←map_map,graph_map_unipotent,hfieldU] at hh
    exact hh
  rw [hnorm]
  constructor
  · change pointRadicalAmbient.map ((MulAut.conj g).toMonoidHom.comp
      ((fieldAutomorphism σ).toMonoidHom.comp graphAut.toMonoidHom))=planeRadicalAmbient
    rw [←map_map,←map_map,graph_point hF hn,field_plane hF hn,conj_plane hF hn hgB]
  · change planeRadicalAmbient.map ((MulAut.conj g).toMonoidHom.comp
      ((fieldAutomorphism σ).toMonoidHom.comp graphAut.toMonoidHom))=pointRadicalAmbient
    rw [←map_map,←map_map,graph_plane hF hn,field_point hF hn,conj_point hF hn hgB]

/-- Setwise stability suffices for central placement: an elementary subgroup
lies in one Sylow wing, and its moving image lies in the other. -/
theorem elementary_le_center_of_moving_actor {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:MulAut (Sp F)) (hU:unipotent.map a.toMonoidHom=unipotent)
    (ha:¬PreservesDiagram a) (V:Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hVU:V≤unipotent) (hV:V.map a.toMonoidHom=V) :
    V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (V.subgroupOf unipotent) := IsElementaryAbelian.subgroupOf hVU
  have hw : V≤pointRadicalAmbient ∨ V≤planeRadicalAmbient := by
    obtain hp|hq := SymplecticConjugatePair.elementary_le_wing (V.subgroupOf unipotent)
    · left
      have hm:=map_mono (f:= (unipotent (F:=F)).subtype) hp
      rw [map_subgroupOf_eq_of_le hVU,←SymplecticConjugatePair.pointRadical_eq_wing] at hm
      exact hm
    · right
      have hm:=map_mono (f:= (unipotent (F:=F)).subtype) hq
      rw [map_subgroupOf_eq_of_le hVU,←SymplecticConjugatePair.planeRadical_eq_wing] at hm
      exact hm
  obtain ⟨hp,hq⟩:=moving_swaps_radicals hF hn a hU ha
  change V≤SymplecticConjugatePair.sylowCenter
  rw [SymplecticConjugatePair.sylowCenter_eq_radical_inf]
  rcases hw with hv|hv
  · have hm:=map_mono (f:=a.toMonoidHom) hv
    rw [hV,hp] at hm
    exact le_inf hv hm
  · have hm:=map_mono (f:=a.toMonoidHom) hv
    rw [hV,hq] at hm
    exact le_inf hm hv

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
